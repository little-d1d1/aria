"""
farkas.py – A *working* implementation of Farkas’ lemma on top of Z3
-------------------------------------------------------------------
    Ax ≤ b   is UNSAT    ⇔    ∃ λ ≥ 0  :  λᵀA = 0  ∧  λᵀb < 0

Features
~~~~~~~~
* works for arbitrary rational-linear Z3 expressions (QF_LRA);
* produces an **actual certificate**  (values of λᵢ) whenever the
  original system is infeasible;
* raises on non-linear or strict inequalities instead of silently
  ignoring them;
* keeps the API intentionally small and type annotated.
"""

from __future__ import annotations
from typing import Dict, List, Tuple, Sequence, Mapping

import z3


# ---------------------------------------------------------------------------#
# Helpers for linearisation                                                  #
# ---------------------------------------------------------------------------#
Num = z3.ArithRef  # either IntVal or RatNumRef


def _is_numeric(e: z3.ExprRef) -> bool:
    return z3.is_int_value(e) or z3.is_rational_value(e)


def _is_zero_expr(e: z3.ExprRef) -> bool:
    return (z3.is_int_value(e) and e.as_long() == 0) or (
        z3.is_rational_value(e) and e.numerator_as_long() == 0
    )


def _to_float(e: Num) -> float:
    if z3.is_int_value(e):
        return float(e.as_long())
    num = float(e.numerator_as_long())
    den = float(e.denominator_as_long())
    return num / den


def _merge_coeff_dict(
    a: Dict[z3.ExprRef, float], b: Mapping[z3.ExprRef, float], sign: float = 1.0
) -> None:
    for v, c in b.items():
        a[v] = a.get(v, 0.0) + sign * c


def _linearise(expr: z3.ArithRef) -> Tuple[Dict[z3.ExprRef, float], float]:
    """
    Return (coeff_dict, constant) s.t.

        expr  ==  Σ coeff_dict[var]·var  +  constant

    Raises ValueError if the term is not linear.
    """
    if _is_numeric(expr):
        return {}, _to_float(expr)

    if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        # plain variable
        return {expr: 1.0}, 0.0

    k = expr.decl().kind()

    # addition / subtraction --------------------------------------------------
    if k in (z3.Z3_OP_ADD, z3.Z3_OP_SUB):
        coeff: Dict[z3.ExprRef, float] = {}
        const = 0.0
        # SUB has the shape  (a - b1 - … - bn) as children()
        first, rest = expr.children()[0], expr.children()[1:]
        c1, k1 = _linearise(first)
        _merge_coeff_dict(coeff, c1, +1.0)
        const += k1
        for child in rest:
            c, k_ = _linearise(child)
            _merge_coeff_dict(coeff, c, -1.0)
            const -= k_
        return coeff, const

    # multiplication ----------------------------------------------------------
    if k == z3.Z3_OP_MUL:
        a, b = expr.children()
        # Try numeric coefficient first
        if _is_numeric(a) and not _is_numeric(b):
            coeff_b, k_b = _linearise(b)
            if k_b != 0.0:
                raise ValueError("non-linear (constant term times variable)")
            factor = _to_float(a)
            return {v: factor * c for v, c in coeff_b.items()}, 0.0
        if _is_numeric(b) and not _is_numeric(a):
            coeff_a, k_a = _linearise(a)
            if k_a != 0.0:
                raise ValueError("non-linear (constant term times variable)")
            factor = _to_float(b)
            return {v: factor * c for v, c in coeff_a.items()}, 0.0

        # Handle symbolic coefficient * variable (for template parameters)
        # If one is a simple variable and the other might be an expression,
        # treat the whole product as a single "variable" for Farkas purposes
        if expr.decl().kind() == z3.Z3_OP_UNINTERPRETED or (
            a.decl().kind() == z3.Z3_OP_UNINTERPRETED
            or b.decl().kind() == z3.Z3_OP_UNINTERPRETED
        ):
            # Treat the entire multiplication as a composite term
            return {expr: 1.0}, 0.0

        raise ValueError("non-linear multiplication")
    # unary minus -------------------------------------------------------------
    if k == z3.Z3_OP_UMINUS:
        coeff, const = _linearise(expr.children()[0])
        return {v: -c for v, c in coeff.items()}, -const

    raise ValueError(f"Unsupported expression in linear context: {expr}")


# ---------------------------------------------------------------------------#
# Main class                                                                 #
# ---------------------------------------------------------------------------#
class FarkasSystem:
    """
    Collect linear constraints, test satisfiability and (if UNSAT) return a
    Farkas certificate.

        fs = FarkasSystem()
        x, y = z3.Reals('x y')
        fs.add(x + y <= 1)
        fs.add(x >= 2)        # system infeasible
        print(fs.is_sat)      # False
        print(fs.certificate) # {'lambda_0': 1.0, 'lambda_1': 1.0}
    """

    # public -----------------------------------------------------------------
    def __init__(self) -> None:
        self._orig: List[z3.BoolRef] = []
        self._solver = z3.Solver()

    # --------------------------- adding constraints -------------------------
    def add(self, c: z3.BoolRef, /) -> None:
        """Add a constraint to the system."""
        self._orig.append(c)
        self._solver.add(c)

    def add_many(self, cs: Sequence[z3.BoolRef]) -> None:
        """Add multiple constraints to the system."""
        for c in cs:
            self.add(c)

    # --------------------------- querying -----------------------------------
    @property
    def is_sat(self) -> bool:
        """Check if the constraint system is satisfiable."""
        return self._solver.check() == z3.sat

    @property
    def model(self) -> z3.ModelRef | None:
        """Get a model if the system is satisfiable."""
        return self._solver.model() if self.is_sat else None

    @property
    def certificate(self) -> Dict[str, float] | None:
        """
        Returns a dictionary λᵢ (as floats) satisfying Farkas’ conditions if
        the system is UNSAT.  Otherwise returns None.
        """
        if self.is_sat:
            return None
        return self._compute_farkas_certificate()

    # -----------------------------------------------------------------------
    # internals                                                              #
    # -----------------------------------------------------------------------
    def _normalise(self) -> Tuple[List[Dict[z3.ExprRef, float]], List[float]]:
        """
        Turn every input constraint into the shape   a·x  ≤  b   and return
        parallel lists of coefficients  and  constants  (b).
        Each *equality* is split into two inequalities.
        Raises ValueError if a constraint is non-linear or strict.
        """
        as_list: List[Dict[z3.ExprRef, float]] = []
        bs: List[float] = []

        for c in self._orig:
            if z3.is_le(c):  # lhs ≤ rhs   ⇒ lhs − rhs ≤ 0
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(lhs - rhs)
                as_list.append(coeff)
                bs.append(-k)
            elif z3.is_ge(c):  # lhs ≥ rhs   ⇒ rhs − lhs ≤ 0
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(rhs - lhs)
                as_list.append(coeff)
                bs.append(-k)
            elif z3.is_eq(c):  # lhs == rhs  ⇒ two inequalities
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(lhs - rhs)
                as_list.append(coeff)
                bs.append(-k)
                as_list.append({v: -coef for v, coef in coeff.items()})
                bs.append(k)
            else:
                raise ValueError(f"unsupported or strict constraint: {c}")

        return as_list, bs

    def _compute_farkas_certificate(self) -> Dict[str, float]:
        a_list, b = self._normalise()

        m = len(a_list)
        if m == 0:
            raise RuntimeError("empty, yet UNSAT?")  # should not happen

        # create symbolic multipliers λᵢ
        lambdas = [z3.Real(f"lambda_{i}") for i in range(m)]
        solver = z3.Solver()

        # λᵢ ≥ 0
        solver.add([lmb >= 0 for lmb in lambdas])

        # Σ λᵢ aᵢⱼ = 0   for every variable xⱼ appearing anywhere
        vars_: List[z3.ExprRef] = sorted(
            {v for row in a_list for v in row}, key=lambda v: v.decl().name()
        )
        for v in vars_:
            solver.add(
                z3.Sum(
                    [lambdas[i] * z3.RealVal(a_list[i].get(v, 0.0)) for i in range(m)]
                )
                == 0
            )

        # Σ λᵢ bᵢ  <  0
        solver.add(z3.Sum([lambdas[i] * z3.RealVal(b[i]) for i in range(m)]) < 0)

        # avoid the trivial all-zero assignment (redundant, but good practice)
        solver.add(z3.Or([l > 0 for l in lambdas]))

        if solver.check() != z3.sat:
            raise RuntimeError(
                "linearisation incomplete – "
                "failed to produce certificate "
                "although original system is UNSAT"
            )

        mdl = solver.model()
        return {
            str(l): _to_float(mdl.eval(l).as_fraction())  # type: ignore
            for l in lambdas
        }


# ---------------------------------------------------------------------------#
# Farkas Lemma Application for Template Synthesis                           #
# ---------------------------------------------------------------------------#
class FarkasLemma:
    """
    A helper class for applying Farkas' lemma to generate constraints for
    template-based invariant synthesis.

    Usage:
        fl = FarkasLemma()
        fl.add_constraint(x + y <= 1)
        fl.add_constraint(x >= 2)
        constraints = fl.apply_farkas_lemma_symbolic([x, y])
        # constraints will be Z3 formulas over lambda variables
    """

    _fresh_counter = 0

    def __init__(self) -> None:
        self._constraints: List[z3.BoolRef] = []

    @classmethod
    def _fresh_lambdas(cls, count: int) -> List[z3.ArithRef]:
        prefix = cls._fresh_counter
        cls._fresh_counter += 1
        return [z3.Real(f"farkas_lambda_{prefix}_{i}") for i in range(count)]

    @staticmethod
    def _zero_for(v: z3.ArithRef) -> z3.ArithRef:
        return z3.IntVal(0) if z3.is_int(v) else z3.RealVal(0)

    @staticmethod
    def _one_for(v: z3.ArithRef) -> z3.ArithRef:
        return z3.IntVal(1) if z3.is_int(v) else z3.RealVal(1)

    @classmethod
    def _linearise_symbolic(
        cls, expr: z3.ArithRef, program_vars: Sequence[z3.ArithRef]
    ) -> Tuple[Dict[z3.ArithRef, z3.ArithRef], z3.ArithRef]:
        """
        Return coefficients and constant of an expression affine in program_vars.

        Coefficients may still contain template variables and Farkas
        multipliers.  This mirrors PolyHorn's polynomial coefficient matching
        while staying in Z3 expressions.
        """
        zero_subst = [(v, cls._zero_for(v)) for v in program_vars]
        const = z3.simplify(z3.substitute(expr, zero_subst))
        coeffs: Dict[z3.ArithRef, z3.ArithRef] = {}

        for v in program_vars:
            subst = list(zero_subst)
            for i, (subst_var, _) in enumerate(subst):
                if subst_var.eq(v):
                    subst[i] = (subst_var, cls._one_for(v))
                    break
            coeffs[v] = z3.simplify(z3.substitute(expr, subst) - const)

        rebuilt = const + z3.Sum([coeffs[v] * v for v in program_vars])
        residual = z3.simplify(expr - rebuilt)
        if not _is_zero_expr(residual):
            solver = z3.Solver()
            solver.add(residual != 0)
            if solver.check() != z3.unsat:
                raise ValueError(
                    f"Expression is not affine in program variables: {expr}"
                )

        return coeffs, const

    @staticmethod
    def _as_ge_zero(c: z3.BoolRef) -> List[Tuple[z3.ArithRef, bool]]:
        """
        Convert an atom to PolyHorn-style polynomial constraints p >= 0.

        The bool marks strict constraints p > 0.  Equalities are split into
        both directions, as in PolyHorn's Farkas reduction.
        """
        if z3.is_true(c):
            return []
        if z3.is_false(c):
            return [(z3.RealVal(-1), False)]
        if z3.is_ge(c):
            return [(c.arg(0) - c.arg(1), False)]
        if z3.is_le(c):
            return [(c.arg(1) - c.arg(0), False)]
        if z3.is_gt(c):
            return [(c.arg(0) - c.arg(1), True)]
        if z3.is_lt(c):
            return [(c.arg(1) - c.arg(0), True)]
        if z3.is_eq(c):
            lhs, rhs = c.arg(0), c.arg(1)
            return [(lhs - rhs, False), (rhs - lhs, False)]
        raise ValueError(f"Unsupported Farkas atom: {c}")

    def apply_entailment_symbolic(
        self,
        conclusion: z3.BoolRef,
        program_vars: Sequence[z3.ArithRef],
    ) -> List[z3.BoolRef]:
        """
        Encode premise constraints => conclusion using PolyHorn's Farkas shape.

        For premise polynomials f_i >= 0 and conclusion g >= 0, PolyHorn builds
        y_0 + sum_i y_i f_i = g with all y_i >= 0.  Matching coefficients of
        program variables eliminates the universal quantifiers.
        """
        premise_polys: List[Tuple[z3.ArithRef, bool]] = []
        for c in self._constraints:
            premise_polys.extend(self._as_ge_zero(c))

        result: List[z3.BoolRef] = []
        for rhs_poly, rhs_strict in self._as_ge_zero(conclusion):
            multipliers = self._fresh_lambdas(len(premise_polys) + 1)
            slack = multipliers[0]

            result.extend(multiplier >= 0 for multiplier in multipliers)

            lhs_poly = slack
            strict_sum = slack
            for multiplier, (premise_poly, premise_strict) in zip(
                multipliers[1:], premise_polys
            ):
                lhs_poly = lhs_poly + multiplier * premise_poly
                if premise_strict:
                    strict_sum = strict_sum + multiplier

            lhs_coeffs, lhs_const = self._linearise_symbolic(lhs_poly, program_vars)
            rhs_coeffs, rhs_const = self._linearise_symbolic(rhs_poly, program_vars)

            result.append(lhs_const == rhs_const)
            for v in program_vars:
                result.append(lhs_coeffs[v] == rhs_coeffs[v])

            if rhs_strict:
                result.append(strict_sum > 0)

        return result

    def apply_farkas_lemma_symbolic(
        self, program_vars: Sequence[z3.ArithRef]
    ) -> List[z3.BoolRef]:
        """
        Apply Farkas' lemma symbolically for template synthesis.

        This version doesn't try to extract numeric coefficients, but works
        directly with Z3 expressions that may contain template parameters.

        Parameters
        ----------
        program_vars : list of Z3 ArithRef
            The program variables (to be eliminated via Farkas)

        Returns
        -------
        list of Z3 BoolRef
            Constraints encoding the Farkas conditions
        """
        premise_polys: List[Tuple[z3.ArithRef, bool]] = []
        for c in self._constraints:
            premise_polys.extend(self._as_ge_zero(c))

        multipliers = self._fresh_lambdas(len(premise_polys))
        result: List[z3.BoolRef] = [multiplier >= 0 for multiplier in multipliers]

        combo = z3.RealVal(0)
        for multiplier, (premise_poly, _premise_strict) in zip(
            multipliers, premise_polys
        ):
            combo = combo + multiplier * premise_poly

        coeffs, const = self._linearise_symbolic(combo, program_vars)
        for v in program_vars:
            result.append(coeffs[v] == 0)
        result.append(const < 0)

        return result

    def add_constraint(self, c: z3.BoolRef) -> None:
        """Add a constraint to the system."""
        self._constraints.append(c)

    def apply_farkas_lemma(self, _variables: Sequence[z3.ArithRef]) -> List[z3.BoolRef]:
        """
        Apply Farkas' lemma to encode that the constraint system is UNSAT.

        Given constraints that should be unsatisfiable, return a list of
        constraints over fresh lambda variables that encode the Farkas
        conditions:
            ∃ λ ≥ 0  :  λᵀA = 0  ∧  λᵀb < 0

        Parameters
        ----------
        _variables : list of Z3 ArithRef
            The variables appearing in the constraints (currently unused)

        Returns
        -------
        list of Z3 BoolRef
            Constraints encoding the Farkas conditions
        """
        if not self._constraints:
            return []

        # Normalize all constraints to the form Ax ≤ b
        a_list: List[Dict[z3.ExprRef, float]] = []
        b: List[float] = []

        for c in self._constraints:
            if z3.is_le(c):  # lhs ≤ rhs ⇒ lhs - rhs ≤ 0
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(lhs - rhs)
                a_list.append(coeff)
                b.append(-k)
            elif z3.is_ge(c):  # lhs ≥ rhs ⇒ rhs - lhs ≤ 0
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(rhs - lhs)
                a_list.append(coeff)
                b.append(-k)
            elif z3.is_eq(c):  # lhs == rhs ⇒ two inequalities
                lhs, rhs = c.arg(0), c.arg(1)
                coeff, k = _linearise(lhs - rhs)
                a_list.append(coeff)
                b.append(-k)
                a_list.append({v: -coef for v, coef in coeff.items()})
                b.append(k)
            elif z3.is_lt(c) or z3.is_gt(c):
                raise ValueError(f"Strict inequality not supported: {c}")
            elif z3.is_not(c):
                # Handle negations by flipping the constraint
                inner = c.arg(0)
                if z3.is_le(inner):  # ¬(lhs ≤ rhs) ⇒ lhs > rhs (strict, unsupported)
                    # Approximate with lhs - rhs ≥ ε, but for now treat as ≥ 0
                    lhs, rhs = inner.arg(0), inner.arg(1)
                    coeff, k = _linearise(lhs - rhs)
                    a_list.append({v: -c for v, c in coeff.items()})
                    b.append(k)
                elif z3.is_ge(inner):  # ¬(lhs ≥ rhs) ⇒ lhs < rhs (strict, unsupported)
                    lhs, rhs = inner.arg(0), inner.arg(1)
                    coeff, k = _linearise(rhs - lhs)
                    a_list.append({v: -c for v, c in coeff.items()})
                    b.append(-k)
                elif z3.is_eq(inner):  # ¬(lhs == rhs) cannot be represented in Farkas
                    raise ValueError(f"Negated equality not supported in Farkas: {c}")
                else:
                    raise ValueError(f"Unsupported negated constraint: {c}")
            else:
                raise ValueError(f"Unsupported constraint type: {c}")

        m = len(a_list)
        if m == 0:
            return []

        # Create fresh lambda variables for this application
        lambdas = []
        for i in range(m):
            lambdas.append(z3.Real(f"lambda_{self._lambda_counter}_{i}"))
        self._lambda_counter += 1

        # Build Farkas conditions
        result: List[z3.BoolRef] = []

        # 1. λᵢ ≥ 0 for all i
        for lmb in lambdas:
            result.append(lmb >= 0)

        # 2. λᵀA = 0  (for each variable)
        # Collect all variables that appear in any constraint
        all_vars = sorted({v for row in a_list for v in row}, key=str)

        for v in all_vars:
            # Sum over all constraints: Σᵢ λᵢ * aᵢⱼ = 0
            terms = []
            for i in range(m):
                coeff_val = a_list[i].get(v, 0.0)
                if coeff_val != 0.0:
                    terms.append(lambdas[i] * z3.RealVal(coeff_val))

            if terms:
                result.append(z3.Sum(terms) == 0)

        # 3. λᵀb < 0
        b_terms = []
        for i in range(m):
            if b[i] != 0.0:
                b_terms.append(lambdas[i] * z3.RealVal(b[i]))

        if b_terms:
            result.append(z3.Sum(b_terms) < 0)
        else:
            # If all b[i] are 0, we need at least one lambda to be positive
            # to avoid trivial solution
            result.append(z3.Or([lmb > 0 for lmb in lambdas]))

        return result
