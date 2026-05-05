"""Fourier-Motzkin quantifier elimination for linear real arithmetic.

This module implements a small, fail-fast existential QE procedure for the
quantifier-free affine fragment over Z3 ``Real`` variables.  The high-level
algorithm is:

1. Normalize Boolean structure to a bounded DNF list of cubes.
2. For each projected Real variable, interpret every affine atom as either a
   lower bound, an upper bound, or a preserved constraint.
3. Replace all lower/upper pairs with the corresponding compatibility
   constraints, which is the Fourier-Motzkin projection step.
4. Reassemble the projected cubes with ``Or`` and continue with the next
   variable.

The implementation intentionally does not try to be a general Z3 arithmetic
normalizer.  Unsupported constructs such as nonlinear arithmetic, mixed
Int/Real terms, nested quantifiers, and excessive DNF expansion raise
``ValueError`` instead of silently returning an unsound result.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Any, Dict, List, Optional, Sequence, Tuple, cast

import z3

from ._projection import get_projection_vars, normalize_vars


MAX_CUBE_COUNT = 64


AffineMap = Dict[int, Tuple[z3.ExprRef, Fraction]]
"""Map from a Z3 variable AST id to ``(variable, rational_coefficient)``."""

Bound = Tuple[AffineMap, Fraction, bool]
"""Affine bound ``expr + const`` plus a strictness bit.

The same representation is used for lower and upper bounds.  The caller tracks
whether a bound is lower or upper; the tuple stores only the right-hand affine
expression and whether the originating comparison was strict.
"""


def _fraction_to_real_val(value: Fraction) -> z3.ArithRef:
    """Convert an exact Python ``Fraction`` to an exact Z3 real numeral."""
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def _merge_affine(target: AffineMap, source: AffineMap, scale: Fraction) -> None:
    """Add ``scale * source`` into ``target`` in-place.

    Coefficients are kept as exact rationals.  Zero coefficients are removed so
    later variable-occurrence checks can use map membership/lookup reliably.
    """
    for var_id, (var, coeff) in source.items():
        new_coeff = target.get(var_id, (var, Fraction(0)))[1] + scale * coeff
        if new_coeff == 0:
            target.pop(var_id, None)
            continue
        target[var_id] = (var, new_coeff)


def _scale_affine(terms: AffineMap, const: Fraction, scale: Fraction) -> Tuple[AffineMap, Fraction]:
    """Return ``scale * (terms + const)`` as a fresh affine representation."""
    scaled_terms: AffineMap = {}
    for var_id, (var, coeff) in terms.items():
        scaled_terms[var_id] = (var, coeff * scale)
    return scaled_terms, const * scale


def _parse_rational_value(expr: z3.ExprRef) -> Optional[Fraction]:
    """Parse a Z3 numeral expression into ``Fraction`` when possible."""
    simplified = z3.simplify(expr)
    if z3.is_int_value(simplified):
        int_value = cast(z3.IntNumRef, simplified)
        return Fraction(int_value.as_long(), 1)
    if z3.is_rational_value(simplified):
        value = cast(z3.RatNumRef, simplified)
        return Fraction(value.numerator_as_long(), value.denominator_as_long())
    return None


def _parse_affine_term(expr: z3.ArithRef) -> Tuple[AffineMap, Fraction]:
    """Parse a supported Z3 arithmetic term as ``sum(coeff_i * x_i) + const``.

    Only Real-sorted affine terms are accepted.  Multiplication is supported
    exactly when one side is a numeral, and division is supported exactly by a
    nonzero numeral.  Anything outside that fragment is rejected.
    """
    if not z3.is_expr(expr):
        raise ValueError("unsupported fragment: expected a Z3 expression")
    if expr.sort().kind() != z3.Z3_REAL_SORT:
        raise ValueError("unsupported fragment: only Real terms are supported")

    constant = _parse_rational_value(expr)
    if constant is not None:
        return {}, constant

    if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return {expr.get_id(): (expr, Fraction(1))}, Fraction(0)

    kind = expr.decl().kind()
    if kind == z3.Z3_OP_ADD:
        total_terms: AffineMap = {}
        total_const = Fraction(0)
        for child in expr.children():
            child_terms, child_const = _parse_affine_term(cast(z3.ArithRef, child))
            _merge_affine(total_terms, child_terms, Fraction(1))
            total_const += child_const
        return total_terms, total_const

    if kind == z3.Z3_OP_SUB:
        children = expr.children()
        first_terms, first_const = _parse_affine_term(cast(z3.ArithRef, children[0]))
        total_terms = dict(first_terms)
        total_const = first_const
        for child in children[1:]:
            child_terms, child_const = _parse_affine_term(cast(z3.ArithRef, child))
            _merge_affine(total_terms, child_terms, Fraction(-1))
            total_const -= child_const
        return total_terms, total_const

    if kind == z3.Z3_OP_UMINUS:
        child_terms, child_const = _parse_affine_term(cast(z3.ArithRef, expr.arg(0)))
        return _scale_affine(child_terms, child_const, Fraction(-1))

    if kind == z3.Z3_OP_MUL:
        children = expr.children()
        if len(children) != 2:
            raise ValueError("unsupported fragment: nonlinear multiplication")
        left_const = _parse_rational_value(children[0])
        right_const = _parse_rational_value(children[1])
        if left_const is not None:
            right_terms, right_term_const = _parse_affine_term(cast(z3.ArithRef, children[1]))
            return _scale_affine(right_terms, right_term_const, left_const)
        if right_const is not None:
            left_terms, left_term_const = _parse_affine_term(cast(z3.ArithRef, children[0]))
            return _scale_affine(left_terms, left_term_const, right_const)
        raise ValueError("unsupported fragment: nonlinear multiplication")

    if kind == z3.Z3_OP_DIV:
        numerator = cast(z3.ArithRef, expr.arg(0))
        denominator = expr.arg(1)
        denominator_const = _parse_rational_value(denominator)
        if denominator_const is None or denominator_const == 0:
            raise ValueError("unsupported fragment: division must be by a nonzero numeral")
        numerator_terms, numerator_const = _parse_affine_term(numerator)
        return _scale_affine(numerator_terms, numerator_const, Fraction(1, 1) / denominator_const)

    raise ValueError("unsupported fragment: nonlinear or non-affine arithmetic term")


def _affine_to_z3(terms: AffineMap, const: Fraction) -> z3.ArithRef:
    """Convert an affine map and constant back to a Z3 arithmetic term."""
    pieces: List[z3.ArithRef] = []
    for var, coeff in terms.values():
        coeff_val = _fraction_to_real_val(coeff)
        if coeff == 1:
            pieces.append(cast(z3.ArithRef, var))
        elif coeff == -1:
            pieces.append(-cast(z3.ArithRef, var))
        else:
            pieces.append(cast(z3.ArithRef, coeff_val * cast(z3.ArithRef, var)))
    if const != 0 or not pieces:
        pieces.append(_fraction_to_real_val(const))
    if len(pieces) == 1:
        return pieces[0]
    return cast(z3.ArithRef, z3.simplify(z3.Sum(pieces)))


def _comparison_from_affine(
    left_terms: AffineMap,
    left_const: Fraction,
    right_terms: AffineMap,
    right_const: Fraction,
    operator: str,
) -> z3.BoolRef:
    """Build a Z3 comparison from two affine representations."""
    left_expr = _affine_to_z3(left_terms, left_const)
    right_expr = _affine_to_z3(right_terms, right_const)
    if operator == "<":
        return left_expr < right_expr
    if operator == "<=":
        return left_expr <= right_expr
    if operator == "==":
        return cast(z3.BoolRef, left_expr == right_expr)
    if operator == ">":
        return left_expr > right_expr
    if operator == ">=":
        return left_expr >= right_expr
    raise ValueError(f"unsupported fragment: unknown operator {operator}")


def _negate_atom(atom: z3.BoolRef) -> z3.BoolRef:
    """Negate a supported arithmetic atom while staying in atom form."""
    kind = atom.decl().kind()
    left = cast(z3.ArithRef, atom.arg(0))
    right = cast(z3.ArithRef, atom.arg(1))
    if kind == z3.Z3_OP_LE:
        return cast(z3.BoolRef, left > right)
    if kind == z3.Z3_OP_LT:
        return cast(z3.BoolRef, left >= right)
    if kind == z3.Z3_OP_GE:
        return cast(z3.BoolRef, left < right)
    if kind == z3.Z3_OP_GT:
        return cast(z3.BoolRef, left <= right)
    if kind == z3.Z3_OP_EQ:
        return z3.Distinct(left, right)
    if kind == z3.Z3_OP_DISTINCT and atom.num_args() == 2:
        return cast(z3.BoolRef, left == right)
    raise ValueError("unsupported fragment: unsupported atom under negation")


def _is_bool_var(expr: z3.ExprRef) -> bool:
    """Return whether ``expr`` is an uninterpreted Boolean variable."""
    return (
        z3.is_const(expr)
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
        and expr.sort().kind() == z3.Z3_BOOL_SORT
    )


def _bool_literal_info(literal: z3.BoolRef) -> Optional[Tuple[z3.BoolRef, bool]]:
    """Return ``(variable, polarity)`` for a Boolean literal, if recognized."""
    if _is_bool_var(literal):
        return cast(z3.BoolRef, literal), True
    if z3.is_not(literal) and _is_bool_var(literal.arg(0)):
        return cast(z3.BoolRef, literal.arg(0)), False
    return None


def _literal_alternatives(literal: z3.BoolRef) -> List[List[z3.BoolRef]]:
    """Return DNF alternatives contributed by one literal-like expression.

    Most supported literals contribute a single one-literal cube.  Disequality
    over reals is the exception: ``a != b`` becomes the two alternatives
    ``a < b`` and ``a > b``.
    """
    if z3.is_true(literal):
        return [[]]
    if z3.is_false(literal):
        return []
    bool_literal = _bool_literal_info(literal)
    if bool_literal is not None:
        return [[literal]]
    if z3.is_not(literal):
        return _literal_alternatives(_negate_atom(cast(z3.BoolRef, literal.arg(0))))

    kind = literal.decl().kind()
    if kind in {z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ}:
        _ = _parse_affine_term(cast(z3.ArithRef, literal.arg(0)))
        _ = _parse_affine_term(cast(z3.ArithRef, literal.arg(1)))
        return [[literal]]
    if kind == z3.Z3_OP_DISTINCT and literal.num_args() == 2:
        left = cast(z3.ArithRef, literal.arg(0))
        right = cast(z3.ArithRef, literal.arg(1))
        _ = _parse_affine_term(left)
        _ = _parse_affine_term(right)
        return [
            [cast(z3.BoolRef, left < right)],
            [cast(z3.BoolRef, left > right)],
        ]
    raise ValueError("unsupported fragment: expected affine arithmetic atoms over Reals")


def _multiply_cube_lists(
    left: List[List[z3.BoolRef]],
    right: List[List[z3.BoolRef]],
    *,
    max_cubes: int,
) -> List[List[z3.BoolRef]]:
    """Conjoin two DNF cube lists, enforcing the configured expansion limit."""
    if not left or not right:
        return []
    if len(left) * len(right) > max_cubes:
        raise ValueError(
            "unsupported fragment: DNF cube expansion exceeds the guarded limit"
        )
    return [list(left_cube) + list(right_cube) for left_cube, right_cube in product(left, right)]


def _expand_to_cubes(expr: z3.BoolRef, *, max_cubes: int) -> List[List[z3.BoolRef]]:
    """Expand a Boolean expression in NNF into bounded DNF cubes."""
    if z3.is_true(expr):
        return [[]]
    if z3.is_false(expr):
        return []
    if z3.is_and(expr):
        cubes = [[]]
        for child in expr.children():
            cubes = _multiply_cube_lists(
                cubes,
                _expand_to_cubes(cast(z3.BoolRef, child), max_cubes=max_cubes),
                max_cubes=max_cubes,
            )
        return cubes
    if z3.is_or(expr):
        cubes: List[List[z3.BoolRef]] = []
        for child in expr.children():
            child_cubes = _expand_to_cubes(cast(z3.BoolRef, child), max_cubes=max_cubes)
            if len(cubes) + len(child_cubes) > max_cubes:
                raise ValueError(
                    "unsupported fragment: DNF cube expansion exceeds the guarded limit"
                )
            cubes.extend(child_cubes)
        return cubes
    return _literal_alternatives(expr)


def _normalize_to_cubes(phi: z3.BoolRef, *, max_cubes: int) -> List[List[z3.BoolRef]]:
    """Simplify to NNF and expand to bounded DNF cubes."""
    if not z3.is_bool(phi):
        raise ValueError("unsupported fragment: phi must be Boolean")
    nnf_phi = z3.Then("simplify", "nnf")(phi).as_expr()
    return _expand_to_cubes(cast(z3.BoolRef, nnf_phi), max_cubes=max_cubes)


def _atom_to_zero_comparison(atom: z3.BoolRef) -> List[Tuple[AffineMap, Fraction, str]]:
    """Normalize an arithmetic atom into comparisons against zero.

    The returned tuples represent ``affine_terms + affine_const <op> 0``.
    Equality is split into both directions so the later FM step only has to
    process ``<`` and ``<=`` style constraints.
    """
    left_terms, left_const = _parse_affine_term(cast(z3.ArithRef, atom.arg(0)))
    right_terms, right_const = _parse_affine_term(cast(z3.ArithRef, atom.arg(1)))

    diff_terms = dict(left_terms)
    _merge_affine(diff_terms, right_terms, Fraction(-1))
    diff_const = left_const - right_const
    kind = atom.decl().kind()
    if kind == z3.Z3_OP_LE:
        return [(diff_terms, diff_const, "<=")]
    if kind == z3.Z3_OP_LT:
        return [(diff_terms, diff_const, "<")]
    if kind == z3.Z3_OP_GE:
        neg_terms, neg_const = _scale_affine(diff_terms, diff_const, Fraction(-1))
        return [(neg_terms, neg_const, "<=")]
    if kind == z3.Z3_OP_GT:
        neg_terms, neg_const = _scale_affine(diff_terms, diff_const, Fraction(-1))
        return [(neg_terms, neg_const, "<")]
    if kind == z3.Z3_OP_EQ:
        neg_terms, neg_const = _scale_affine(diff_terms, diff_const, Fraction(-1))
        return [(diff_terms, diff_const, "<="), (neg_terms, neg_const, "<=")]
    raise ValueError("unsupported fragment: expected normalized affine atom")


def _extract_bound(
    zero_terms: AffineMap,
    zero_const: Fraction,
    var: z3.ExprRef,
    operator: str,
) -> Tuple[str, Bound]:
    """Extract a bound on ``var`` from ``zero_terms + zero_const <op> 0``.

    If the coefficient of ``var`` is positive, the normalized inequality gives
    an upper bound.  If it is negative, division by the coefficient flips the
    direction and gives a lower bound.
    """
    coeff = zero_terms.get(var.get_id(), (var, Fraction(0)))[1]
    if coeff == 0:
        raise ValueError("internal error: attempted to extract a bound without the variable")

    residual_terms = dict(zero_terms)
    residual_terms.pop(var.get_id(), None)
    scale = Fraction(-1, 1) / coeff
    bound_terms, bound_const = _scale_affine(residual_terms, zero_const, scale)
    strict = operator == "<"
    if coeff > 0:
        return ("upper", (bound_terms, bound_const, strict))
    return ("lower", (bound_terms, bound_const, strict))


def _combine_bounds(lower: Bound, upper: Bound) -> z3.BoolRef:
    """Build the FM compatibility constraint ``lower <= upper``.

    The combined comparison is strict whenever either contributing bound is
    strict, matching real arithmetic semantics.
    """
    lower_terms, lower_const, lower_strict = lower
    upper_terms, upper_const, upper_strict = upper
    operator = "<" if lower_strict or upper_strict else "<="
    return _comparison_from_affine(
        lower_terms,
        lower_const,
        upper_terms,
        upper_const,
        operator,
    )


def _eliminate_var_from_cube(cube: Sequence[z3.BoolRef], var: z3.ExprRef) -> z3.BoolRef:
    """Project one Real variable from one conjunction of literals."""
    preserved: List[z3.BoolRef] = []
    lowers: List[Bound] = []
    uppers: List[Bound] = []

    for atom in cube:
        if _bool_literal_info(atom) is not None:
            preserved.append(atom)
            continue
        for zero_terms, zero_const, operator in _atom_to_zero_comparison(atom):
            coeff = zero_terms.get(var.get_id(), (var, Fraction(0)))[1]
            if coeff == 0:
                preserved.append(
                    _comparison_from_affine(
                        zero_terms,
                        zero_const,
                        {},
                        Fraction(0),
                        "<=" if operator == "<=" else "<",
                    )
                )
                continue

            bound_kind, bound = _extract_bound(zero_terms, zero_const, var, operator)
            if bound_kind == "lower":
                lowers.append(bound)
            else:
                uppers.append(bound)

    # FM projection: a witness for ``var`` exists exactly when every collected
    # lower bound is compatible with every collected upper bound.  If either
    # side is missing, the variable can be chosen unboundedly in that direction.
    if lowers and uppers:
        for lower in lowers:
            for upper in uppers:
                preserved.append(_combine_bounds(lower, upper))

    if not preserved:
        return z3.BoolVal(True)
    return cast(z3.BoolRef, z3.simplify(z3.And(preserved)))


def _eliminate_bool_var_from_cube(cube: Sequence[z3.BoolRef], var: z3.ExprRef) -> z3.BoolRef:
    """Project one Boolean variable from one conjunction of literals."""
    preserved: List[z3.BoolRef] = []
    literal_polarities: Dict[int, bool] = {}

    for literal in cube:
        info = _bool_literal_info(literal)
        if info is None:
            preserved.append(literal)
            continue

        bool_var, polarity = info
        previous = literal_polarities.get(bool_var.get_id())
        if previous is not None and previous != polarity:
            return z3.BoolVal(False)
        literal_polarities[bool_var.get_id()] = polarity

        if bool_var.get_id() == var.get_id():
            continue
        preserved.append(literal)

    if not preserved:
        return z3.BoolVal(True)
    return cast(z3.BoolRef, z3.simplify(z3.And(preserved)))


def _validate_projection_vars(
    vars_to_check: Sequence[z3.ExprRef], *, allow_bool: bool
) -> None:
    """Validate variables used by the projection API.

    Explicit quantified variables for this FM entry point must be Real.  Boolean
    variables are accepted only for partial projection of free variables when
    ``keep_vars`` is used.
    """
    allowed_sorts = {z3.Z3_REAL_SORT}
    if allow_bool:
        allowed_sorts.add(z3.Z3_BOOL_SORT)

    for var in vars_to_check:
        if not z3.is_const(var) or var.decl().kind() != z3.Z3_OP_UNINTERPRETED:
            raise ValueError(
                "unsupported fragment: quantified and kept items must be variables"
            )
        if var.sort().kind() not in allowed_sorts:
            raise ValueError(
                "unsupported fragment: only Real and Boolean variables are supported"
            )


def _contains_quantifier(expr: z3.ExprRef) -> bool:
    """Return whether an expression tree contains any Z3 quantifier node."""
    stack = [expr]
    seen = set()
    while stack:
        current = stack.pop()
        ast_id = current.get_id()
        if ast_id in seen:
            continue
        seen.add(ast_id)
        if z3.is_quantifier(current):
            return True
        stack.extend(current.children())
    return False


def qelim_exists_lra_fm(
    phi: Any, qvars: Any, *, keep_vars: Optional[Any] = None
) -> z3.BoolRef:
    """Eliminate existentially quantified Real variables with Fourier-Motzkin.

    Args:
        phi: Quantifier-free Boolean Z3 formula in the supported affine LRA
            fragment.
        qvars: One Real variable or an iterable of Real variables to eliminate.
        keep_vars: Optional partial-projection whitelist.  When provided, every
            free variable in ``phi`` that is not in ``keep_vars`` is projected
            away together with ``qvars``.  Boolean free variables may be
            projected this way, but explicit ``qvars`` must be Real variables.

    Returns:
        A quantifier-free Z3 ``BoolRef`` equivalent to ``Exists(qvars, phi)`` or
        to the corresponding partial projection when ``keep_vars`` is provided.

    Raises:
        ValueError: If the input leaves the supported fragment, contains nested
            quantifiers, has invalid projection variables, or exceeds the DNF
            cube expansion guard.
    """
    if not z3.is_bool(phi):
        raise ValueError("unsupported fragment: phi must be a Boolean Z3 formula")
    if _contains_quantifier(cast(z3.ExprRef, phi)):
        raise ValueError("unsupported fragment: nested quantifiers are not supported")

    normalized_qvars = normalize_vars(qvars)
    normalized_keep_vars = normalize_vars(keep_vars) if keep_vars is not None else None
    projection_vars = get_projection_vars(phi, normalized_qvars, normalized_keep_vars)

    _validate_projection_vars(normalized_qvars, allow_bool=False)
    _validate_projection_vars(projection_vars, allow_bool=True)
    if normalized_keep_vars is not None:
        _validate_projection_vars(normalized_keep_vars, allow_bool=True)

    result = cast(z3.BoolRef, phi)

    # Variables are eliminated one at a time.  Re-normalizing after each step
    # keeps the next projection simple and lets Z3 simplify contradictions or
    # tautologies introduced by the previous FM combination.
    for var in projection_vars:
        cubes = _normalize_to_cubes(cast(z3.BoolRef, result), max_cubes=MAX_CUBE_COUNT)
        if var.sort().kind() == z3.Z3_BOOL_SORT:
            eliminated_cubes = [_eliminate_bool_var_from_cube(cube, var) for cube in cubes]
        else:
            eliminated_cubes = [_eliminate_var_from_cube(cube, var) for cube in cubes]
        result = z3.simplify(z3.Or(eliminated_cubes))

    return cast(z3.BoolRef, z3.simplify(result))
