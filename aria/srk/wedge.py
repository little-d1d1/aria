"""
Convex polyhedra (wedge) implementation for SRK.

This module provides abstract domain operations for convex polyhedra using
the APRON library for polyhedral operations and analysis.
Based on the OCaml implementation in src/wedge.ml.
"""

import logging
from typing import List, Dict, Set, Tuple, Optional, Any, Union, Callable
from dataclasses import dataclass
from enum import Enum
from functools import reduce

from . import linear
from . import syntax
from . import smt as Smt
from . import interpretation
from . import srkSimplify
from . import nonlinear
from . import apron as ApronInterface
from . import coordinateSystem as CS
from . import polynomial as P
from .polynomial import RewriteSystem

logger = logging.getLogger(__name__)


# APRON types (simplified)
class Scalar:
    Float = "Float"
    Mpqf = "Mpqf"
    Mpfrf = "Mpfrf"


class Coeff:
    Scalar = "Scalar"
    Interval = "Interval"


class Abstract0:
    def __init__(self, manager, int_dim: int, real_dim: int, srk=None):
        self.manager = manager
        self.int_dim = int_dim
        self.real_dim = real_dim
        self._constraints: List[Lincons0] = []
        self._is_bottom: bool = False
        self._srk = srk  # Optional SRK context for Z3-based checks

    @staticmethod
    def top(manager, int_dim: int, real_dim: int, srk=None):
        obj = Abstract0(manager, int_dim, real_dim, srk)
        obj._constraints = []
        obj._is_bottom = False
        return obj

    @staticmethod
    def bottom(manager, int_dim: int, real_dim: int, srk=None):
        obj = Abstract0(manager, int_dim, real_dim, srk)
        obj._constraints = []
        obj._is_bottom = True
        return obj

    @staticmethod
    def of_lincons_array(manager, int_dim, real_dim, lincons_array, srk=None):
        obj = Abstract0(manager, int_dim, real_dim, srk)
        obj._constraints = list(lincons_array)
        obj._is_bottom = False
        return obj

    @staticmethod
    def is_top(manager, abstract):
        return not abstract._is_bottom and len(abstract._constraints) == 0

    @staticmethod
    def is_bottom(manager, abstract):
        if abstract._is_bottom:
            return True
        if not abstract._constraints:
            return False
        # Use Z3 to check satisfiability if srk context is available
        if abstract._srk is not None:
            srk = abstract._srk
            n_dims = abstract.int_dim + abstract.real_dim
            dim_vars = []
            for i in range(n_dims):
                sym = syntax.mk_symbol(srk, f"_apron_d{i}", syntax.Type.REAL)
                dim_vars.append(syntax.mk_const(srk, sym))
            formulas = []
            for lc in abstract._constraints:
                terms = []
                for coeff, dim in lc.linexpr0.coeffs:
                    if dim is not None and dim < len(dim_vars):
                        coeff_term = syntax.mk_real(srk, coeff)
                        terms.append(syntax.mk_mul(srk, [coeff_term, dim_vars[dim]]))
                cst = lc.linexpr0.get_cst()
                if cst is not None:
                    terms.append(syntax.mk_real(srk, cst))
                if len(terms) > 1:
                    lin_term = syntax.mk_add(srk, terms)
                elif len(terms) == 1:
                    lin_term = terms[0]
                else:
                    lin_term = syntax.mk_real(srk, linear.QQ.zero())
                zero = syntax.mk_real(srk, linear.QQ.zero())
                if lc.typ == Lincons0.EQ:
                    formulas.append(syntax.mk_eq(srk, lin_term, zero))
                elif lc.typ == Lincons0.SUPEQ:
                    formulas.append(syntax.mk_leq(srk, zero, lin_term))
                elif lc.typ == Lincons0.SUP:
                    formulas.append(syntax.mk_lt(srk, zero, lin_term))
            if formulas:
                formula = syntax.mk_and(srk, formulas)
                result = Smt.is_sat(srk, formula)
                return result == Smt.Unsat
        return False

    @staticmethod
    def is_eq(manager, abstract1, abstract2):
        if abstract1._is_bottom and abstract2._is_bottom:
            return True
        if abstract1._is_bottom != abstract2._is_bottom:
            return False
        # Compare constraint sets (order-independent)
        c1 = [(lc.typ, tuple(lc.linexpr0.coeffs), lc.linexpr0.get_cst())
               for lc in abstract1._constraints]
        c2 = [(lc.typ, tuple(lc.linexpr0.coeffs), lc.linexpr0.get_cst())
               for lc in abstract2._constraints]
        return set(c1) == set(c2)

    @staticmethod
    def add_dimensions(manager, abstract, dim: "Dim", project: bool):
        # Create a new Abstract0 with updated dimensions
        new_int = abstract.int_dim + dim.intdim
        new_real = abstract.real_dim + dim.realdim
        result = Abstract0(manager, new_int, new_real, abstract._srk)
        result._constraints = list(abstract._constraints)
        result._is_bottom = abstract._is_bottom
        return result

    @staticmethod
    def remove_dimensions(manager, abstract, dim: "Dim"):
        result = Abstract0(manager, abstract.int_dim, abstract.real_dim, abstract._srk)
        result._constraints = list(abstract._constraints)
        result._is_bottom = abstract._is_bottom
        return result

    @staticmethod
    def meet_lincons_array(manager, abstract, lincons_array):
        result = Abstract0(manager, abstract.int_dim, abstract.real_dim, abstract._srk)
        result._constraints = list(abstract._constraints) + list(lincons_array)
        result._is_bottom = abstract._is_bottom
        return result

    @staticmethod
    def join(manager, abstract1, abstract2):
        # If either is bottom, return the other
        if abstract1._is_bottom:
            result = Abstract0(manager, abstract2.int_dim, abstract2.real_dim,
                               abstract2._srk)
            result._constraints = list(abstract2._constraints)
            result._is_bottom = abstract2._is_bottom
            return result
        if abstract2._is_bottom:
            result = Abstract0(manager, abstract1.int_dim, abstract1.real_dim,
                               abstract1._srk)
            result._constraints = list(abstract1._constraints)
            result._is_bottom = abstract1._is_bottom
            return result
        # Join: keep only constraints present in both (intersection of constraint sets)
        c1 = {(lc.typ, tuple(lc.linexpr0.coeffs), lc.linexpr0.get_cst())
               for lc in abstract1._constraints}
        c2 = {(lc.typ, tuple(lc.linexpr0.coeffs), lc.linexpr0.get_cst())
               for lc in abstract2._constraints}
        common = c1 & c2
        srk = abstract1._srk or abstract2._srk
        result = Abstract0(manager, abstract1.int_dim, abstract1.real_dim, srk)
        result._constraints = [lc for lc in abstract1._constraints
                               if (lc.typ, tuple(lc.linexpr0.coeffs),
                                   lc.linexpr0.get_cst()) in common]
        result._is_bottom = False
        return result

    @staticmethod
    def to_lincons_array(manager, abstract):
        return list(abstract._constraints)


class Linexpr0:
    def __init__(self, coeffs: List[Tuple], cst: Optional):
        self.coeffs = coeffs
        self.cst = cst

    @staticmethod
    def of_list(project, coeffs, cst):
        return Linexpr0(coeffs, cst)

    def iter(self, f):
        for coeff, dim in self.coeffs:
            f(coeff, dim)
        if self.cst:
            f(self.cst, None)

    def get_cst(self):
        return self.cst

    def set_coeff(self, dim, coeff):
        # Update coefficient for dimension
        pass


class Lincons0:
    EQ = "EQ"
    SUPEQ = "SUPEQ"
    SUP = "SUP"
    DISEQ = "DISEQ"
    EQMOD = "EQMOD"

    def __init__(self, linexpr0, typ: str):
        self.linexpr0 = linexpr0
        self.typ = typ

    @staticmethod
    def make(linexpr0, typ: str):
        return Lincons0(linexpr0, typ)


class Dim:
    def __init__(self, dim: List[int], intdim: int, realdim: int):
        self.dim = dim
        self.intdim = intdim
        self.realdim = realdim


# Manager for APRON operations
def get_manager():
    """Get APRON manager (Polka strict)"""
    return "PolkaManager"  # Placeholder


# Environment for coordinate system mapping
@dataclass
class Environment:
    """Environment mapping coordinates to APRON dimensions"""

    int_dim: List[int]  # Integer coordinate IDs
    real_dim: List[int]  # Real coordinate IDs

    def copy(self) -> "Environment":
        return Environment(self.int_dim.copy(), self.real_dim.copy())


@dataclass
class Wedge:
    """Convex polyhedron (wedge) representation"""

    srk: syntax.Context  # SRK context
    cs: CS.CoordinateSystem  # Coordinate system
    env: Environment  # Environment mapping
    abstract: Abstract0  # APRON abstract value

    def is_consistent(self) -> bool:
        """Check if environment is consistent with coordinate system"""
        return CS.dim(self.cs) == len(self.env.int_dim) + len(self.env.real_dim)

    def update_env(self) -> None:
        """Update environment when coordinate system grows"""
        int_dim = len(self.env.int_dim)
        real_dim = len(self.env.real_dim)

        if int_dim + real_dim < CS.dim(self.cs):
            added_int = 0
            added_real = 0

            for id in range(int_dim + real_dim, CS.dim(self.cs)):
                match CS.type_of_id(self.cs, id):
                    case syntax.TyInt:
                        added_int += 1
                        self.env.int_dim.append(id)
                    case syntax.TyReal:
                        added_real += 1
                        self.env.real_dim.append(id)

            logger.debug(
                f"update env: adding {added_int} integer and {added_real} real dimension(s)"
            )

            added = [
                int_dim if i < added_int else int_dim + real_dim
                for i in range(added_int + added_real)
            ]

            # Add dimensions to APRON abstract value
            self.abstract = Abstract0.add_dimensions(
                get_manager(), self.abstract, Dim(added, added_int, added_real), False
            )


# Utility functions
def qq_of_scalar(scalar) -> linear.QQ:
    """Convert APRON scalar to QQ"""
    match scalar:
        case Scalar.Float(k):
            return linear.QQ.of_float(k)
        case Scalar.Mpqf(k):
            return k
        case Scalar.Mpfrf(k):
            return linear.QQ.from_mpfrf(k)


def qq_of_coeff(coeff) -> Optional[linear.QQ]:
    """Convert APRON coefficient to QQ"""
    match coeff:
        case Coeff.Scalar(s):
            return qq_of_scalar(s)
        case Coeff.Interval(_):
            return None


def qq_of_coeff_exn(coeff) -> linear.QQ:
    """Convert APRON coefficient to QQ (raises exception if interval)"""
    match coeff:
        case Coeff.Scalar(s):
            return qq_of_scalar(s)
        case Coeff.Interval(_):
            raise ValueError("qq_of_coeff_exn: argument must be a scalar")


def coeff_of_qq(qq: linear.QQ) -> str:
    """Convert QQ to APRON coefficient"""
    return Coeff.Scalar(Scalar.Mpqf(qq))


def mk_log(srk: syntax.Context) -> syntax.Symbol:
    """Get log symbol"""
    return nonlinear.mk_log(srk)


def mk_pow(srk: syntax.Context) -> syntax.Symbol:
    """Get pow symbol"""
    return nonlinear.mk_pow(srk)


def vec_of_poly(poly: P.Polynomial) -> Optional[linear.QQVector]:
    """Convert polynomial to vector if linear"""
    # This would need proper polynomial vector conversion
    return None


def poly_of_vec(vec: linear.QQVector) -> P.Polynomial:
    """Convert vector to polynomial"""
    # This would need proper vector polynomial conversion
    return P.zero()


# Environment operations
def mk_empty_env() -> Environment:
    """Create empty environment"""
    return Environment([], [])


def mk_env(cs: CS.CoordinateSystem) -> Environment:
    """Create environment from coordinate system"""
    env = mk_empty_env()
    for id in range(CS.dim(cs)):
        match CS.type_of_id(cs, id):
            case syntax.TyInt:
                env.int_dim.append(id)
            case syntax.TyReal:
                env.real_dim.append(id)
    return env


# Wedge operations
def top(srk: syntax.Context) -> Wedge:
    """Create top wedge (universe)"""
    cs = CS.mk_empty(srk)
    return Wedge(srk, cs, mk_empty_env(), Abstract0.top(get_manager(), 0, 0))


def is_top(wedge: Wedge) -> bool:
    """Check if wedge is top"""
    return Abstract0.is_top(get_manager(), wedge.abstract)


def bottom(srk: syntax.Context) -> Wedge:
    """Create bottom wedge (empty)"""
    cs = CS.mk_empty(srk)
    return Wedge(srk, cs, mk_empty_env(), Abstract0.bottom(get_manager(), 0, 0))


def is_bottom(wedge: Wedge) -> bool:
    """Check if wedge is bottom"""
    return Abstract0.is_bottom(get_manager(), wedge.abstract)


def copy(wedge: Wedge) -> Wedge:
    """Copy a wedge"""
    return Wedge(wedge.srk, CS.copy(wedge.cs), wedge.env.copy(), wedge.abstract)


def equal(wedge1: Wedge, wedge2: Wedge) -> bool:
    """Check if two wedges are equal"""
    srk = wedge1.srk
    phi = nonlinear.uninterpret(srk, to_formula(wedge1))
    phi_prime = nonlinear.uninterpret(srk, to_formula(wedge2))

    return (
        Smt.is_sat(srk, syntax.mk_not(srk, syntax.mk_iff(srk, phi, phi_prime)))
        == Smt.Unsat
    )


def to_atoms(wedge: Wedge) -> List[syntax.Formula]:
    """Convert wedge to list of atomic formulas.

    Retrieves all linear constraints stored in the abstract domain and
    converts each one to an SRK formula via :func:`atom_of_lincons`.
    """
    lincons_array = Abstract0.to_lincons_array(get_manager(), wedge.abstract)
    return [atom_of_lincons(wedge, lc) for lc in lincons_array]


def to_formula(wedge: Wedge) -> syntax.Formula:
    """Convert wedge to formula"""
    return syntax.mk_and(wedge.srk, to_atoms(wedge))


# APRON conversion functions
def vec_of_linexpr(env: Environment, linexpr: Linexpr0) -> linear.QQVector:
    """Convert APRON linexpr to vector"""
    vec = linear.QQVector.zero()

    for coeff, dim in linexpr.coeffs:
        qq_coeff = qq_of_coeff(coeff)
        if qq_coeff is not None and not linear.QQ.equal(qq_coeff, linear.QQ.zero()):
            # Map dimension back to coordinate ID
            if dim < len(env.int_dim):
                coord_id = env.int_dim[dim]
            else:
                coord_id = env.real_dim[dim - len(env.int_dim)]
            vec = linear.QQVector.add_term(qq_coeff, coord_id, vec)

    qq_cst = qq_of_coeff(linexpr.cst)
    if qq_cst is not None:
        vec = linear.QQVector.add_term(qq_cst, CS.const_id, vec)

    return vec


def linexpr_of_vec(
    cs: CS.CoordinateSystem, env: Environment, vec: linear.QQVector
) -> Linexpr0:
    """Convert vector to APRON linexpr"""

    def mk_coeff_dim(coeff, id):
        coord_id = CS.dim_of_id(cs, env, id)
        return (coeff_of_qq(coeff), coord_id)

    const_coeff, rest = linear.QQVector.pivot(CS.const_id, vec)
    coeffs = [mk_coeff_dim(coeff, id) for coeff, id in linear.QQVector.enum(rest)]
    # Pass None if constant coefficient is zero, otherwise pass the coefficient
    cst_value = (
        None
        if linear.QQ.equal(const_coeff, linear.QQ.zero())
        else coeff_of_qq(const_coeff)
    )
    return Linexpr0.of_list(None, coeffs, cst_value)


def atom_of_lincons(wedge: Wedge, lincons: Lincons0) -> syntax.Formula:
    """Convert APRON lincons to atomic formula"""
    term = CS.term_of_vec(wedge.cs, vec_of_linexpr(wedge.env, lincons.linexpr0))
    zero = syntax.mk_real(wedge.srk, linear.QQ.zero())

    match lincons.typ:
        case Lincons0.EQ:
            return syntax.mk_eq(wedge.srk, term, zero)
        case Lincons0.SUPEQ:
            return syntax.mk_leq(wedge.srk, zero, term)
        case Lincons0.SUP:
            return syntax.mk_lt(wedge.srk, zero, term)
        case _:
            raise ValueError(f"Unsupported lincons type: {lincons.typ}")


def pp(formatter, wedge: Wedge) -> None:
    """Pretty print wedge"""
    formatter.write(f"Wedge with {CS.dim(wedge.cs)} dimensions")


def show(wedge: Wedge) -> str:
    """String representation of wedge"""
    return f"Wedge({CS.dim(wedge.cs)} dims)"


def lincons_of_atom(
    srk: syntax.Context, cs: CS.CoordinateSystem, env: Environment, atom: syntax.Formula
) -> Lincons0:
    """Convert atomic formula to APRON lincons"""
    match interpretation.destruct_atom(srk, atom):
        case ("ArithComparison", ("Lt", x, y)):
            vec = linear.QQVector.add(
                CS.vec_of_term(cs, y), linear.QQVector.negate(CS.vec_of_term(cs, x))
            )
            return Lincons0.make(linexpr_of_vec(cs, env, vec), Lincons0.SUP)
        case ("ArithComparison", ("Leq", x, y)):
            vec = linear.QQVector.add(
                CS.vec_of_term(cs, y), linear.QQVector.negate(CS.vec_of_term(cs, x))
            )
            return Lincons0.make(linexpr_of_vec(cs, env, vec), Lincons0.SUPEQ)
        case ("ArithComparison", ("Eq", x, y)):
            vec = linear.QQVector.add(
                CS.vec_of_term(cs, y), linear.QQVector.negate(CS.vec_of_term(cs, x))
            )
            return Lincons0.make(linexpr_of_vec(cs, env, vec), Lincons0.EQ)
        case _:
            raise ValueError(f"Unsupported atom type: {atom}")


def meet_atoms(wedge: Wedge, atoms: List[syntax.Formula]) -> None:
    """Meet wedge with atomic formulas"""
    # Ensure coordinate system admits all atoms
    for atom in atoms:
        match interpretation.destruct_atom(wedge.srk, atom):
            case ("ArithComparison", (_, x, y)):
                CS.admit_term(wedge.cs, x)
                CS.admit_term(wedge.cs, y)
            case _:
                pass

    wedge.update_env()

    # Convert atoms to APRON lincons
    lincons_array = [
        lincons_of_atom(wedge.srk, wedge.cs, wedge.env, atom) for atom in atoms
    ]

    # Meet with APRON abstract value
    wedge.abstract = Abstract0.meet_lincons_array(
        get_manager(), wedge.abstract, lincons_array
    )


def bound_vec(wedge: Wedge, vec: linear.QQVector) -> "Interval":
    """Compute bounds for vector expression from stored constraints.

    Iterates over all constraints in the Abstract0 and finds those whose
    non-constant part is a scalar multiple of *vec*.  From each matching
    constraint we extract a lower or upper bound on *vec* and return the
    tightest interval.
    """
    from fractions import Fraction
    _Interval = Interval  # local alias; will be the real class after Edit B

    if Abstract0.is_bottom(get_manager(), wedge.abstract):
        return _Interval.bottom()

    constraints = Abstract0.to_lincons_array(get_manager(), wedge.abstract)
    if not constraints:
        return _Interval.top()

    lower: Optional[Fraction] = None
    upper: Optional[Fraction] = None

    # Decompose vec into (constant_part, non_constant_part)
    vec_cst, vec_rest = linear.QQVector.pivot(CS.const_id, vec) if CS.const_id in vec.entries else (linear.QQ.zero(), vec)

    for lc in constraints:
        # Build a dict of (dim -> coeff) for the constraint, excluding constant
        lc_coeffs: Dict[int, Any] = {}
        lc_cst = linear.QQ.zero()
        for coeff, dim in lc.linexpr0.coeffs:
            if dim is not None:
                lc_coeffs[dim] = coeff
            else:
                lc_cst = coeff
        cst_val = lc.linexpr0.get_cst()
        if cst_val is not None:
            lc_cst = cst_val

        # Check if lc_coeffs is a scalar multiple of vec_rest
        # We need: lc_coeffs = k * vec_rest for some k
        vec_rest_entries = {d: c for d, c in vec_rest.entries.items() if c != 0}
        lc_nonzero = {d: c for d, c in lc_coeffs.items() if c != 0}

        if not vec_rest_entries and not lc_nonzero:
            # Both are constant-only; skip (constraint is purely about constants)
            continue
        if not vec_rest_entries or not lc_nonzero:
            continue

        # Check dimension set match
        if set(vec_rest_entries.keys()) != set(lc_nonzero.keys()):
            continue

        # Compute k = lc_coeffs[d] / vec_rest[d] for any dimension d
        ref_dim = next(iter(vec_rest_entries.keys()))
        vec_ref = vec_rest_entries[ref_dim]
        if vec_ref == 0:
            continue
        k = lc_nonzero[ref_dim] / vec_ref

        # Verify k works for all dimensions
        match = True
        for d in vec_rest_entries:
            expected = k * vec_rest_entries[d]
            actual = lc_nonzero[d]
            if expected != actual:
                match = False
                break
        if not match:
            continue

        # Now: k * vec + lc_cst [typ] 0
        # For SUPEQ: k * vec + lc_cst >= 0  =>  k * vec >= -lc_cst
        # For SUP:   k * vec + lc_cst > 0   =>  k * vec > -lc_cst (approximate as >=)
        # For EQ:    k * vec + lc_cst = 0    =>  vec = -lc_cst / k
        if k == 0:
            continue
        neg_cst_over_k = -lc_cst / k

        if lc.typ == Lincons0.EQ:
            # Equality gives both upper and lower
            lower = neg_cst_over_k if lower is None else max(lower, neg_cst_over_k)
            upper = neg_cst_over_k if upper is None else min(upper, neg_cst_over_k)
        elif lc.typ in (Lincons0.SUPEQ, Lincons0.SUP):
            if k > 0:
                # k * vec >= -lc_cst  =>  vec >= -lc_cst / k  (lower bound)
                lower = neg_cst_over_k if lower is None else max(lower, neg_cst_over_k)
            else:
                # k * vec >= -lc_cst with k < 0  =>  vec <= -lc_cst / k  (upper bound)
                upper = neg_cst_over_k if upper is None else min(upper, neg_cst_over_k)

    return _Interval.make(lower, upper)


def bound_coordinate(wedge: Wedge, coordinate: int) -> "Interval":
    """Compute bounds for coordinate"""
    return bound_vec(wedge, linear.QQVector.of_term(linear.QQ.one(), coordinate))


def bound_monomial(wedge: Wedge, monomial) -> "Interval":
    """Compute bounds for monomial"""
    # This would need proper interval arithmetic for monomials
    # For now, return placeholder
    return Interval.const(linear.QQ.one())


def symbolic_bounds(
    wedge: Wedge, symbol
) -> Tuple[List[syntax.Formula], List[syntax.Formula]]:
    """Compute symbolic lower and upper bounds for *symbol*.

    Returns ``(lower_bounds, upper_bounds)`` where each list contains SRK
    terms representing the bound expressions.  For a constraint
    ``a*sym + rest + c >= 0`` with ``a != 0``:

    - ``a > 0``  =>  ``sym >= -(rest + c) / a``  (lower bound)
    - ``a < 0``  =>  ``sym <= -(rest + c) / a``  (upper bound)
    """
    srk = wedge.srk
    cs = wedge.cs

    # Find the coordinate ID for the symbol
    sym_term = syntax.mk_const(srk, symbol)
    sym_vec = cs.vec_of_term(sym_term, admit=False)

    # The symbol should map to a single-dimension vector {coord_id: 1}
    non_const = {d: c for d, c in sym_vec.entries.items() if d != CS.const_id}
    if not non_const:
        return ([], [])

    sym_dim = next(iter(non_const.keys()))
    sym_coeff = non_const[sym_dim]

    lower_bounds = []
    upper_bounds = []

    constraints = Abstract0.to_lincons_array(get_manager(), wedge.abstract)
    for lc in constraints:
        # Build coefficient dict from linexpr
        lc_coeffs: Dict[int, Any] = {}
        lc_cst = linear.QQ.zero()
        for coeff, dim in lc.linexpr0.coeffs:
            if dim is not None:
                lc_coeffs[dim] = coeff
            else:
                lc_cst = coeff
        cst_val = lc.linexpr0.get_cst()
        if cst_val is not None:
            lc_cst = cst_val

        if sym_dim not in lc_coeffs:
            continue

        a = lc_coeffs[sym_dim]
        if a == 0:
            continue

        # Build "rest" vector: all coefficients except sym_dim
        rest_entries = {d: c for d, c in lc_coeffs.items() if d != sym_dim}
        rest_entries[CS.const_id] = lc_cst
        rest_vec = linear.QQVector(rest_entries)

        # Bound term = -rest / a   (as a formula)
        # We express it as a term: -(rest_term) / a
        rest_term = cs._vector_to_term(rest_vec)
        neg_rest = syntax.mk_neg(srk, rest_term)
        a_term = syntax.mk_real(srk, abs(a))
        bound_term = syntax.mk_div(srk, neg_rest, a_term) if a != linear.QQ.one() else neg_rest

        if lc.typ in (Lincons0.EQ, Lincons0.SUPEQ, Lincons0.SUP):
            if a > 0:
                # sym >= bound
                lower_bounds.append(bound_term)
            else:
                # sym <= bound
                upper_bounds.append(bound_term)

    return (lower_bounds, upper_bounds)


# Interval arithmetic — delegates to the real Interval implementation.
from aria.srk.interval import Interval as _Interval


class Interval:
    """Facade over :class:`aria.srk.interval.Interval`.

    Static-method API used throughout wedge.py; every returned / accepted
    interval value is a real ``_Interval`` instance.
    """

    @staticmethod
    def top():
        return _Interval.top()

    @staticmethod
    def bottom():
        return _Interval.bottom()

    @staticmethod
    def const(qq: linear.QQ):
        return _Interval.const(linear.QQ(qq))

    @staticmethod
    def make(lower, upper):
        return _Interval.make(
            linear.QQ(lower) if lower is not None else None,
            linear.QQ(upper) if upper is not None else None,
        )

    @staticmethod
    def of_apron(apron_interval):
        """Convert an APRON interval to a real Interval."""
        # APRON intervals typically have (lower, upper) attributes
        try:
            lo = apron_interval.lower if apron_interval.lower is not None else None
            hi = apron_interval.upper if apron_interval.upper is not None else None
            return _Interval.make(
                linear.QQ(lo) if lo is not None else None,
                linear.QQ(hi) if hi is not None else None,
            )
        except Exception:
            return _Interval.top()

    @staticmethod
    def elem(qq: linear.QQ, interval) -> bool:
        """Check whether *qq* belongs to *interval*."""
        if isinstance(interval, _Interval):
            return interval.contains(linear.QQ(qq))
        return False

    @staticmethod
    def is_nonnegative(interval) -> bool:
        if isinstance(interval, _Interval):
            if interval.is_bottom():
                return False
            return interval.lower is not None and interval.lower >= 0
        return False

    @staticmethod
    def is_nonpositive(interval) -> bool:
        if isinstance(interval, _Interval):
            if interval.is_bottom():
                return False
            return interval.upper is not None and interval.upper <= 0
        return False

    @staticmethod
    def is_positive(interval) -> bool:
        if isinstance(interval, _Interval):
            if interval.is_bottom():
                return False
            return interval.lower is not None and interval.lower > 0
        return False

    @staticmethod
    def is_negative(interval) -> bool:
        if isinstance(interval, _Interval):
            if interval.is_bottom():
                return False
            return interval.upper is not None and interval.upper < 0
        return False

    @staticmethod
    def lower(interval) -> Optional[linear.QQ]:
        if isinstance(interval, _Interval):
            return interval.lower
        return None

    @staticmethod
    def upper(interval) -> Optional[linear.QQ]:
        if isinstance(interval, _Interval):
            return interval.upper
        return None

    @staticmethod
    def mul(ivl1, ivl2):
        if isinstance(ivl1, _Interval) and isinstance(ivl2, _Interval):
            return ivl1 * ivl2
        return _Interval.top()

    @staticmethod
    def add(ivl1, ivl2):
        if isinstance(ivl1, _Interval) and isinstance(ivl2, _Interval):
            return ivl1 + ivl2
        return _Interval.top()

    @staticmethod
    def exp_const(ivl, power: int):
        """Raise *ivl* to an integer *power*."""
        if isinstance(ivl, _Interval):
            if ivl.is_bottom():
                return _Interval.bottom()
            if ivl.is_point():
                try:
                    val = ivl.lower ** power
                    return _Interval.const(linear.QQ(val))
                except Exception:
                    return _Interval.top()
            # Conservative: use point-interval power for positive intervals
            if Interval.is_nonnegative(ivl) and power == 2:
                lo = linear.QQ(0) if ivl.lower is None else (ivl.lower ** 2 if ivl.lower >= 0 else linear.QQ(0))
                hi = None if ivl.upper is None else ivl.upper ** 2
                return _Interval.make(lo, hi)
        return _Interval.top()

    @staticmethod
    def div(ivl1, ivl2):
        if isinstance(ivl1, _Interval) and isinstance(ivl2, _Interval):
            if ivl1.is_bottom() or ivl2.is_bottom():
                return _Interval.bottom()
            return ivl1 / ivl2
        return _Interval.top()

    @staticmethod
    def log(base_ivl, exp_ivl):
        """Approximate logarithm interval (conservative: returns top)."""
        return _Interval.top()


def mk_sign_axioms(srk: syntax.Context) -> syntax.Formula:
    """Create sign axioms for nonlinear operations"""
    # This would create the full set of sign axioms
    # For now, return a placeholder
    return syntax.mk_true(srk)


def wedge_entails(wedge: Wedge, phi: syntax.Formula) -> bool:
    """Check if wedge entails formula modulo LIRA + sign axioms"""
    srk = wedge.srk
    s = Smt.mk_solver(srk)
    Smt.Solver.add(
        s,
        [
            nonlinear.uninterpret(srk, to_formula(wedge)),
            nonlinear.uninterpret(srk, syntax.mk_not(srk, phi)),
            mk_sign_axioms(srk),
        ],
    )

    match Smt.Solver.check(s, []):
        case Smt.Sat | Smt.Unknown:
            return False
        case Smt.Unsat:
            return True


def nonnegative_polynomial(wedge: Wedge, p: P.Polynomial) -> bool:
    """Check if polynomial is nonnegative on wedge"""
    term = CS.term_of_polynomial(wedge.cs, p)
    geq_zero = syntax.mk_leq(
        wedge.srk, syntax.mk_real(wedge.srk, linear.QQ.zero()), term
    )
    return wedge_entails(wedge, geq_zero)


def bound_polynomial(wedge: Wedge, polynomial: P.Polynomial) -> "Interval":
    """Compute bounds for polynomial"""
    # This would need proper polynomial interval arithmetic
    # For now, return placeholder
    return Interval.top()


def affine_hull(wedge: Wedge) -> List[linear.QQVector]:
    """Compute affine hull of wedge.

    Extracts all equality (EQ) constraints from the abstract domain and
    converts each linear expression into a :class:`linear.QQVector`.
    The returned vectors *v* satisfy ``v = 0`` in the affine hull.
    """
    if is_bottom(wedge):
        return [
            linear.QQVector.add_term(
                linear.QQ.one(), CS.const_id, linear.QQVector.zero()
            )
        ]

    lincons_array = Abstract0.to_lincons_array(get_manager(), wedge.abstract)
    result = []
    for lc in lincons_array:
        if lc.typ == Lincons0.EQ:
            vec = vec_of_linexpr(wedge.env, lc.linexpr0)
            result.append(vec)
    return result


def polynomial_constraints(
    lemma: Callable, wedge: Wedge
) -> List[Tuple[str, P.Polynomial]]:
    """Extract polynomial constraints from wedge"""
    # This would extract constraints from APRON lincons
    # For now, return placeholder
    return []


def polynomial_cone(lemma: Callable, wedge: Wedge) -> List[P.Polynomial]:
    """Extract polynomial cone from wedge"""
    constraints = polynomial_constraints(lemma, wedge)
    return [p for _, p in constraints if _ in ("Nonneg", "Pos")]


def vanishing_ideal(wedge: Wedge) -> List[P.Polynomial]:
    """Compute vanishing ideal of wedge.

    Returns the list of polynomials that vanish on the wedge.  Each
    equality vector from :func:`affine_hull` is converted to a polynomial
    via the coordinate system's :meth:`polynomial_of_vec`.
    """
    if is_bottom(wedge):
        return [P.one()]

    eq_vectors = affine_hull(wedge)
    result = []
    for vec in eq_vectors:
        poly = wedge.cs.polynomial_of_vec(vec)
        if not poly.is_zero():
            result.append(poly)
    return result


def coordinate_ideal(lemma: Callable, wedge: Wedge) -> List[P.Polynomial]:
    """Compute coordinate ideal of wedge.

    Starts with the :func:`vanishing_ideal` and adds defining polynomials
    for every *compound* coordinate (Mul, App, Inv, Mod, Floor).
    For a coordinate ``c`` whose defining expression is ``e``, the
    polynomial ``c - e`` is added to the ideal.
    """
    cs = wedge.cs
    result = list(vanishing_ideal(wedge))

    for coord_id in range(cs.dim):
        cs_term = cs.destruct_coordinate(coord_id)
        # Compound terms are those whose definition involves other coordinates
        if cs_term.term_type in (
            CS.CSTermType.MUL,
            CS.CSTermType.INV,
            CS.CSTermType.MOD,
            CS.CSTermType.FLOOR,
            CS.CSTermType.APP,
        ):
            coord_poly = cs.polynomial_of_coordinate(coord_id)
            # defining poly: coord_id - expr(coord_id)
            coord_var = P.Polynomial.of_dim(coord_id, cs.dim)
            defining = coord_var - coord_poly
            if not defining.is_zero():
                result.append(defining)

    return result


def equational_saturation(lemma: Callable, wedge: Wedge) -> P.RewriteSystem:
    """Compute equational saturation of wedge.

    Builds a Gröbner-basis rewrite system from the :func:`coordinate_ideal`
    and iterates until no new equalities are discovered:

    1. For each coordinate *i*, reduce ``polynomial_of_coordinate(i)`` with
       the current basis.
    2. If reduction yields a *linear* polynomial ``p`` with ``p = 0``, add
       it as an EQ constraint to the wedge (via :func:`meet_atoms`).
    3. Recompute the affine hull; if new vanishing polynomials appear, add
       them to the ideal and recompute the Gröbner basis.
    4. Repeat until saturated.

    Returns the final :class:`P.RewriteSystem`.
    """
    cs = wedge.cs
    srk = wedge.srk

    # --- helper: convert a linear polynomial to a QQVector ---
    def _vec_of_linear_poly(poly: P.Polynomial) -> Optional[linear.QQVector]:
        if poly.degree() > 1:
            return None
        vec = linear.QQVector.zero()
        for monom, coeff in poly.terms.items():
            # Monomial entries map dim -> exponent
            total_exp = sum(monom.exponents) if hasattr(monom, 'exponents') else 0
            if total_exp == 0:
                # constant term
                vec = linear.QQVector.add_term(coeff, CS.const_id, vec)
            elif total_exp == 1:
                # single variable with exponent 1
                for d, e in enumerate(monom.exponents):
                    if e == 1:
                        vec = linear.QQVector.add_term(coeff, d, vec)
                        break
        return vec

    # --- helper: add an equality polynomial as a wedge constraint ---
    def _add_equality(poly: P.Polynomial):
        vec = _vec_of_linear_poly(poly)
        if vec is not None:
            linexpr = linexpr_of_vec(cs, wedge.env, vec)
            lc = Lincons0.make(linexpr, Lincons0.EQ)
            wedge.abstract = Abstract0.meet_lincons_array(
                get_manager(), wedge.abstract, [lc]
            )

    # 1. Build initial ideal
    gens = coordinate_ideal(lemma, wedge)
    if not gens:
        return P.RewriteSystem([])

    ideal = P.Ideal(gens)
    prev_vanishing = set(id(p) for p in vanishing_ideal(wedge))
    max_iters = 20

    for _ in range(max_iters):
        basis = ideal.groebner_basis()

        # 2. For each coordinate, reduce its polynomial; add new equalities
        changed = False
        for coord_id in range(cs.dim):
            coord_poly = cs.polynomial_of_coordinate(coord_id)
            reduced = basis.reduce(coord_poly)
            if reduced.is_zero():
                continue
            # If reduced polynomial is linear and non-trivial, add as equality
            if reduced.degree() <= 1:
                vec = _vec_of_linear_poly(reduced)
                if vec is not None and not vec.is_zero():
                    _add_equality(reduced)
                    changed = True

        # 3. Recompute affine hull and check for new vanishing polynomials
        new_vanishing = vanishing_ideal(wedge)
        new_polys = [p for p in new_vanishing if id(p) not in prev_vanishing]
        if new_polys:
            for p in new_polys:
                prev_vanishing.add(id(p))
            ideal = P.Ideal(ideal.generators + new_polys)
            changed = True

        if not changed:
            break

    return ideal.groebner_basis()


def generalized_fourier_motzkin(lemma: Callable, order, wedge: Wedge) -> None:
    """Apply generalized Fourier-Motzkin elimination"""
    srk = wedge.srk
    cs = wedge.cs

    def add_bound(precondition, bound):
        logger.debug(f"Lemma: {precondition} => {bound}")
        lemma(syntax.mk_or(srk, [syntax.mk_not(srk, precondition), bound]))
        meet_atoms(wedge, [bound])

    old_wedge = bottom(srk)

    def polyhedron_equal(w1, w2):
        return CS.dim(w1.cs) == CS.dim(w2.cs) and Abstract0.is_eq(
            get_manager(), w1.abstract, w2.abstract
        )

    gfm_limit = 10  # Maximum iterations
    iterations = 0

    while iterations < gfm_limit and not polyhedron_equal(wedge, old_wedge):
        iterations += 1
        logger.debug(f"GFM iteration: {iterations}")
        old_wedge = copy(wedge)
        cone = polynomial_cone(lemma, wedge)

        for p in cone:
            c, m, p_rest = P.split_leading(order, p)
            if linear.QQ.lt(c, linear.QQ.zero()):
                p_scaled = P.scalar_mul(linear.QQ.negate(linear.QQ.inverse(c)), p)

                for q in cone:
                    quot, rem = P.qr_monomial(q, m)
                    if P.degree(quot) >= 1 and nonnegative_polynomial(wedge, quot):
                        zero = syntax.mk_real(srk, linear.QQ.zero())
                        mk_nonneg = lambda t: syntax.mk_leq(srk, zero, t)

                        p_sub_m = P.add_term(linear.QQ.of_int(-1), m, p_scaled)
                        hypothesis = syntax.mk_and(
                            srk,
                            [
                                mk_nonneg(CS.term_of_polynomial(cs, p_sub_m)),
                                mk_nonneg(CS.term_of_polynomial(cs, quot)),
                                mk_nonneg(CS.term_of_polynomial(cs, q)),
                            ],
                        )

                        conclusion = mk_nonneg(
                            CS.term_of_polynomial(cs, P.add(P.mul(quot, p_scaled), rem))
                        )
                        add_bound(hypothesis, conclusion)


def strengthen_intervals(lemma: Callable, wedge: Wedge) -> None:
    """Strengthen intervals using bounds"""
    srk = wedge.srk
    cs = wedge.cs
    zero = syntax.mk_real(srk, linear.QQ.zero())

    # Compute bounds for each coordinate and add them as constraints
    for id in range(CS.dim(cs)):
        vec = linear.QQVector.of_term(linear.QQ.one(), id)
        ivl = bound_vec(wedge, vec)

        # Add lower bound constraint if available
        lower = Interval.lower(ivl)
        if lower is not None:
            term = CS.term_of_vec(cs, vec)
            lower_bound = syntax.mk_leq(srk, syntax.mk_real(srk, lower), term)
            if not wedge_entails(wedge, lower_bound):
                lemma(lower_bound)
                meet_atoms(wedge, [lower_bound])

        # Add upper bound constraint if available
        upper = Interval.upper(ivl)
        if upper is not None:
            term = CS.term_of_vec(cs, vec)
            upper_bound = syntax.mk_leq(srk, term, syntax.mk_real(srk, upper))
            if not wedge_entails(wedge, upper_bound):
                lemma(upper_bound)
                meet_atoms(wedge, [upper_bound])


def strengthen_products(lemma: Callable, rewrite, wedge: Wedge) -> None:
    """Strengthen products using rewrite rules"""
    srk = wedge.srk
    cs = wedge.cs
    zero = syntax.mk_real(srk, linear.QQ.zero())

    # For each pair of coordinates, check if their product has better bounds
    # This is a simplified implementation - full version would use sophisticated
    # interval arithmetic and polynomial rewriting
    for id1 in range(CS.dim(cs)):
        for id2 in range(id1 + 1, CS.dim(cs)):
            vec1 = linear.QQVector.of_term(linear.QQ.one(), id1)
            vec2 = linear.QQVector.of_term(linear.QQ.one(), id2)

            ivl1 = bound_vec(wedge, vec1)
            ivl2 = bound_vec(wedge, vec2)

            # Compute product interval
            prod_ivl = Interval.mul(ivl1, ivl2)

            # Check if product is zero (one of the intervals contains only zero)
            if Interval.elem(linear.QQ.zero(), prod_ivl) and (
                Interval.elem(linear.QQ.zero(), ivl1)
                or Interval.elem(linear.QQ.zero(), ivl2)
            ):
                # Add constraint that product is zero if one factor is zero
                term1 = CS.term_of_vec(cs, vec1)
                term2 = CS.term_of_vec(cs, vec2)
                constraint = syntax.mk_or(
                    srk,
                    [
                        syntax.mk_not(srk, syntax.mk_eq(srk, term1, zero)),
                        syntax.mk_not(srk, syntax.mk_eq(srk, term2, zero)),
                        syntax.mk_eq(srk, syntax.mk_mul(srk, [term1, term2]), zero),
                    ],
                )
                lemma(constraint)


def strengthen_integral(lemma: Callable, wedge: Wedge) -> None:
    """Strengthen integral dimensions"""
    srk = wedge.srk
    cs = wedge.cs

    # For integer dimensions, add integrality constraints
    for id in range(CS.dim(cs)):
        if CS.type_of_id(cs, id) == syntax.TyInt:
            vec = linear.QQVector.of_term(linear.QQ.one(), id)
            ivl = bound_vec(wedge, vec)

            # Get lower and upper bounds
            lower = Interval.lower(ivl)
            upper = Interval.upper(ivl)

            if lower is not None and upper is not None:
                # Strengthen to integer bounds using floor/ceiling
                lower_int = linear.QQ.of_int(int(linear.QQ.ceiling(lower)))
                upper_int = linear.QQ.of_int(int(linear.QQ.floor(upper)))

                # Add strengthened bounds if they're tighter
                term = CS.term_of_vec(cs, vec)

                if linear.QQ.gt(lower_int, lower):
                    lower_bound = syntax.mk_leq(
                        srk, syntax.mk_real(srk, lower_int), term
                    )
                    if not wedge_entails(wedge, lower_bound):
                        lemma(lower_bound)
                        meet_atoms(wedge, [lower_bound])

                if linear.QQ.lt(upper_int, upper):
                    upper_bound = syntax.mk_leq(
                        srk, term, syntax.mk_real(srk, upper_int)
                    )
                    if not wedge_entails(wedge, upper_bound):
                        lemma(upper_bound)
                        meet_atoms(wedge, [upper_bound])


def strengthen_inverse(lemma: Callable, wedge: Wedge) -> None:
    """Strengthen inverse coordinates"""
    srk = wedge.srk
    cs = wedge.cs
    zero = syntax.mk_real(srk, linear.QQ.zero())
    one = syntax.mk_real(srk, linear.QQ.one())

    # For each coordinate, check if we can deduce bounds on its inverse
    for id in range(CS.dim(cs)):
        vec = linear.QQVector.of_term(linear.QQ.one(), id)
        ivl = bound_vec(wedge, vec)

        # Check if the interval is bounded away from zero
        if Interval.is_positive(ivl) or Interval.is_negative(ivl):
            # Can safely compute inverse interval
            term = CS.term_of_vec(cs, vec)

            # If x > 0, then 1/x is also bounded
            if Interval.is_positive(ivl):
                lower = Interval.lower(ivl)
                upper = Interval.upper(ivl)

                if (
                    lower is not None
                    and upper is not None
                    and not linear.QQ.equal(lower, linear.QQ.zero())
                ):
                    # 1/upper <= 1/x <= 1/lower (when x > 0)
                    inv_lower = (
                        linear.QQ.inverse(upper)
                        if not linear.QQ.equal(upper, linear.QQ.zero())
                        else None
                    )
                    inv_upper = (
                        linear.QQ.inverse(lower)
                        if not linear.QQ.equal(lower, linear.QQ.zero())
                        else None
                    )

                    inv_term = syntax.mk_div(srk, one, term)

                    if inv_lower is not None:
                        inv_lower_bound = syntax.mk_leq(
                            srk, syntax.mk_real(srk, inv_lower), inv_term
                        )
                        lemma(inv_lower_bound)

                    if inv_upper is not None:
                        inv_upper_bound = syntax.mk_leq(
                            srk, inv_term, syntax.mk_real(srk, inv_upper)
                        )
                        lemma(inv_upper_bound)


def strengthen(lemma: Callable, wedge: Wedge) -> None:
    """Strengthen wedge using various techniques"""
    nonlinear.ensure_symbols(wedge.srk)

    if not wedge.is_consistent():
        return

    logger.debug(f"Before strengthen: {wedge}")

    rewrite = equational_saturation(lemma, wedge)

    strengthen_intervals(lemma, wedge)
    strengthen_inverse(lemma, wedge)

    # More strengthening operations would go here

    ignore_result = equational_saturation(lemma, wedge)  # Final saturation
    logger.debug(f"After strengthen: {wedge}")


def of_atoms(srk: syntax.Context, atoms: List[syntax.Formula]) -> Wedge:
    """Create wedge from atomic formulas"""
    cs = CS.mk_empty(srk)

    # Register terms in coordinate system
    for atom in atoms:
        match interpretation.destruct_atom(srk, atom):
            case ("ArithComparison", (_, x, y)):
                CS.admit_term(cs, x)
                CS.admit_term(cs, y)
            case _:
                pass

    env = mk_env(cs)
    abstract = Abstract0.of_lincons_array(
        get_manager(),
        len(env.int_dim),
        len(env.real_dim),
        [lincons_of_atom(srk, cs, env, atom) for atom in atoms],
    )

    wedge = Wedge(srk, cs, env, abstract)
    wedge.update_env()
    return wedge


def common_cs(wedge1: Wedge, wedge2: Wedge) -> Tuple[Wedge, Wedge]:
    """Create common coordinate system for two wedges"""
    srk = wedge1.srk
    cs = CS.mk_empty(srk)

    # Register all terms from both wedges
    for atom in to_atoms(wedge1):
        match interpretation.destruct_atom(srk, atom):
            case ("ArithComparison", (_, x, y)):
                CS.admit_term(cs, x)
                CS.admit_term(cs, y)
            case _:
                pass

    for atom in to_atoms(wedge2):
        match interpretation.destruct_atom(srk, atom):
            case ("ArithComparison", (_, x, y)):
                CS.admit_term(cs, x)
                CS.admit_term(cs, y)
            case _:
                pass

    env = mk_env(cs)
    env2 = mk_env(cs)

    # Create wedges with common coordinate system
    wedge1_new = Wedge(
        srk,
        cs,
        env,
        Abstract0.of_lincons_array(
            get_manager(),
            len(env.int_dim),
            len(env.real_dim),
            [lincons_of_atom(srk, cs, env, atom) for atom in to_atoms(wedge1)],
        ),
    )
    wedge2_new = Wedge(
        srk,
        cs,
        env2,
        Abstract0.of_lincons_array(
            get_manager(),
            len(env.int_dim),
            len(env.real_dim),
            [lincons_of_atom(srk, cs, env, atom) for atom in to_atoms(wedge2)],
        ),
    )

    return wedge1_new, wedge2_new


def join(lemma: Callable, wedge1: Wedge, wedge2: Wedge) -> Wedge:
    """Join two wedges"""
    if is_bottom(wedge1):
        return copy(wedge2)
    elif is_bottom(wedge2):
        return copy(wedge1)

    wedge1_copy, wedge2_copy = common_cs(wedge1, wedge2)
    strengthen(lemma, wedge1_copy)
    wedge2_copy.update_env()
    strengthen(lemma, wedge2_copy)
    wedge1_copy.update_env()  # May have grown during strengthening

    return Wedge(
        wedge1_copy.srk,
        wedge1_copy.cs,
        wedge1_copy.env,
        Abstract0.join(get_manager(), wedge1_copy.abstract, wedge2_copy.abstract),
    )


def meet(wedge1: Wedge, wedge2: Wedge) -> Wedge:
    """Meet two wedges"""
    if is_top(wedge1):
        return copy(wedge2)
    elif is_top(wedge2):
        return copy(wedge1)

    wedge_copy = copy(wedge1)
    meet_atoms(wedge_copy, to_atoms(wedge2))
    return wedge_copy


def abstract_to_wedge(srk: syntax.Context, phi: syntax.Formula) -> Wedge:
    """Abstract formula to wedge"""
    return abstract_subwedge(
        lambda lemma, w: w,
        lambda lemma, w1, w2: join(lemma, w1, w2),
        lambda w: to_formula(w),
        srk,
        phi,
    )


def abstract_subwedge(
    of_wedge: Callable,
    join_op: Callable,
    to_formula_op: Callable,
    srk: syntax.Context,
    phi: syntax.Formula,
) -> Any:
    """Abstract formula using custom wedge operations"""
    phi = syntax.eliminate_ite(srk, phi)
    phi = simplify.simplify_terms(srk, phi)

    logger.info(f"Abstracting formula: {phi}")

    solver = Smt.mk_solver(srk, theory="QF_LIRA")
    uninterp_phi = syntax.rewrite(
        srk, phi, down=syntax.nnf_rewriter(srk), up=nonlinear.uninterpret_rewriter(srk)
    )

    # lin_phi, nonlinear_map = srk_simplify.purify(srk, uninterp_phi)  # Disabled due to missing functions
    lin_phi = uninterp_phi  # Placeholder
    nonlinear_map = {}  # Placeholder

    def go(prop):
        blocking_clause = to_formula_op(prop)
        blocking_clause = nonlinear.uninterpret(srk, blocking_clause)
        blocking_clause = syntax.mk_not(srk, blocking_clause)

        logger.debug(f"Blocking clause: {blocking_clause}")
        Smt.Solver.add(solver, [blocking_clause])

        match Smt.Solver.get_model(solver):
            case Smt.Unsat:
                return prop
            case Smt.Unknown:
                logger.warning("Symbolic abstraction failed; returning top")
                return of_wedge(lambda w: top(srk))
            case Smt.Sat(model):
                # implicant = interpretation.select_implicant(model, lin_phi)  # Disabled due to missing functions
                implicant = []  # Placeholder
                if implicant is None:
                    raise AssertionError("No implicant found")

                # Create new wedge from implicant
                new_wedge = of_atoms(srk, implicant)
                new_wedge = strengthen(
                    lambda psi: Smt.Solver.add(
                        solver, [nonlinear.uninterpret(srk, psi)]
                    ),
                    new_wedge,
                )

                new_prop = of_wedge(lambda w: new_wedge)
                return go(
                    join_op(
                        lambda psi: Smt.Solver.add(
                            solver, [nonlinear.uninterpret(srk, psi)]
                        ),
                        prop,
                        new_prop,
                    )
                )

    result = go(of_wedge(lambda w: bottom(srk)))
    logger.info(f"Abstraction result: {to_formula_op(result)}")
    return result


class WedgeElement:
    """Element of a wedge (convex polyhedron) domain."""

    def __init__(self, context, constraints):
        """Initialize wedge element with constraints."""
        self.context = context
        self.constraints = constraints

    def join(self, other):
        """Join with another wedge element."""
        # Simplified implementation - just union of constraints
        combined_constraints = self.constraints + other.constraints
        return WedgeElement(self.context, combined_constraints)

    def meet(self, other):
        """Meet with another wedge element."""
        # Simplified implementation - intersection of constraints
        combined_constraints = self.constraints + other.constraints
        return WedgeElement(self.context, combined_constraints)

    def exists(self, variables):
        """Existential quantification over variables."""
        # Simplified implementation - just return self
        # In a full implementation, this would eliminate the quantified variables
        return self

    def is_bottom(self):
        """Check if this wedge is bottom (empty)."""
        # Simplified implementation - assume non-empty if has constraints
        # In a full implementation, this would check for satisfiability
        return len(self.constraints) == 0

    def project(self, variables):
        """Project onto a subset of variables."""
        # Simplified implementation - just return self
        # In a full implementation, this would perform variable elimination
        return self

    def strengthen(self, additional_constraints):
        """Strengthen with additional constraints."""
        # Add the additional constraints
        combined_constraints = self.constraints + additional_constraints
        return WedgeElement(self.context, combined_constraints)

    def to_atoms(self):
        """Convert wedge to atomic formulas."""
        return self.constraints

    def __str__(self):
        return f"WedgeElement({len(self.constraints)} constraints)"


class WedgeDomain:
    """Domain of wedge elements."""

    def __init__(self, context):
        """Initialize wedge domain."""
        self.context = context

    def top(self):
        """Top element (universe)."""
        return WedgeElement(self.context, [])

    def bottom(self):
        """Bottom element (empty)."""
        # Bottom would be represented by contradictory constraints
        return WedgeElement(self.context, [])

    def join(self, other):
        """Join with another wedge domain."""
        # Simplified implementation - just return self
        # In a full implementation, this would compute the join of two domains
        return self

    def meet(self, other):
        """Meet with another wedge domain."""
        # Simplified implementation - just return self
        # In a full implementation, this would compute the meet of two domains
        return self

    def __str__(self):
        return f"WedgeDomain({self.context})"
