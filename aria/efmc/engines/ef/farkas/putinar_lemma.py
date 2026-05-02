"""Z3-facing Putinar encoding for EFMC template constraints."""

from __future__ import annotations

from itertools import product
from typing import Dict, List, Sequence, Tuple

import z3


Degree = Tuple[int, ...]
Polynomial = Dict[Degree, z3.ArithRef]


def _is_numeric(e: z3.ExprRef) -> bool:
    return z3.is_int_value(e) or z3.is_rational_value(e) or z3.is_algebraic_value(e)


def _zero() -> z3.ArithRef:
    return z3.RealVal(0)


def _one() -> z3.ArithRef:
    return z3.RealVal(1)


def _is_zero_expr(e: z3.ExprRef) -> bool:
    simplified = z3.simplify(e)
    return (z3.is_int_value(simplified) and simplified.as_long() == 0) or (
        z3.is_rational_value(simplified) and simplified.numerator_as_long() == 0
    )


def _const_poly(value: z3.ArithRef, arity: int) -> Polynomial:
    return {tuple([0] * arity): value}


def _var_poly(index: int, arity: int) -> Polynomial:
    degree = [0] * arity
    degree[index] = 1
    return {tuple(degree): _one()}


def _add_poly(left: Polynomial, right: Polynomial) -> Polynomial:
    result = dict(left)
    for degree, coeff in right.items():
        result[degree] = z3.simplify(result.get(degree, _zero()) + coeff)
    return {
        degree: coeff
        for degree, coeff in result.items()
        if not _is_zero_expr(coeff)
    }


def _neg_poly(poly: Polynomial) -> Polynomial:
    return {degree: z3.simplify(-coeff) for degree, coeff in poly.items()}


def _sub_poly(left: Polynomial, right: Polynomial) -> Polynomial:
    return _add_poly(left, _neg_poly(right))


def _mul_poly(left: Polynomial, right: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for left_degree, left_coeff in left.items():
        for right_degree, right_coeff in right.items():
            degree = tuple(a + b for a, b in zip(left_degree, right_degree))
            coeff = z3.simplify(left_coeff * right_coeff)
            result[degree] = z3.simplify(result.get(degree, _zero()) + coeff)
    return {
        degree: coeff
        for degree, coeff in result.items()
        if not _is_zero_expr(coeff)
    }


class PutinarLemma:
    """
    Encode polynomial entailments with Putinar-style SOS certificates.

    Given premises f_i(x) >= 0 and a conclusion g(x) >= 0, the generated
    constraints search for SOS polynomials h_i such that:

        h_0 + sum_i h_i * f_i = g

    This is the Z3-expression analogue of aria.quant.polyhorn.Putinar.
    """

    _fresh_counter = 0

    def __init__(self, max_degree: int = 2) -> None:
        if max_degree < 0:
            raise ValueError("max_degree must be non-negative")
        self.max_degree = max_degree
        self._constraints: List[z3.BoolRef] = []

    def add_constraint(self, constraint: z3.BoolRef) -> None:
        self._constraints.append(constraint)

    @classmethod
    def _fresh_real(cls, stem: str) -> z3.ArithRef:
        name = f"putinar_{stem}_{cls._fresh_counter}"
        cls._fresh_counter += 1
        return z3.Real(name)

    @staticmethod
    def _as_ge_zero(constraint: z3.BoolRef) -> List[Tuple[z3.ArithRef, bool]]:
        if z3.is_true(constraint):
            return []
        if z3.is_false(constraint):
            return [(z3.RealVal(-1), False)]
        if z3.is_ge(constraint):
            return [(constraint.arg(0) - constraint.arg(1), False)]
        if z3.is_le(constraint):
            return [(constraint.arg(1) - constraint.arg(0), False)]
        if z3.is_gt(constraint):
            return [(constraint.arg(0) - constraint.arg(1), True)]
        if z3.is_lt(constraint):
            return [(constraint.arg(1) - constraint.arg(0), True)]
        if z3.is_eq(constraint):
            lhs, rhs = constraint.arg(0), constraint.arg(1)
            return [(lhs - rhs, False), (rhs - lhs, False)]
        raise ValueError(f"Unsupported Putinar atom: {constraint}")

    @staticmethod
    def _monomial_degrees(arity: int, max_degree: int) -> List[Degree]:
        degrees: List[Degree] = []
        for degree in product(range(max_degree + 1), repeat=arity):
            if sum(degree) <= max_degree:
                degrees.append(tuple(degree))
        return degrees

    def _expr_to_poly(
        self, expr: z3.ArithRef, program_vars: Sequence[z3.ArithRef]
    ) -> Polynomial:
        arity = len(program_vars)
        for index, var in enumerate(program_vars):
            if expr.eq(var):
                return _var_poly(index, arity)

        if _is_numeric(expr):
            return _const_poly(expr, arity)

        kind = expr.decl().kind()
        if kind == z3.Z3_OP_TO_REAL:
            return self._expr_to_poly(expr.arg(0), program_vars)
        if kind == z3.Z3_OP_UNINTERPRETED:
            return _const_poly(expr, arity)
        if kind == z3.Z3_OP_UMINUS:
            return _neg_poly(self._expr_to_poly(expr.arg(0), program_vars))
        if kind == z3.Z3_OP_ADD:
            result = _const_poly(_zero(), arity)
            for child in expr.children():
                result = _add_poly(result, self._expr_to_poly(child, program_vars))
            return result
        if kind == z3.Z3_OP_SUB:
            children = expr.children()
            result = self._expr_to_poly(children[0], program_vars)
            for child in children[1:]:
                result = _sub_poly(result, self._expr_to_poly(child, program_vars))
            return result
        if kind == z3.Z3_OP_MUL:
            result = _const_poly(_one(), arity)
            for child in expr.children():
                result = _mul_poly(result, self._expr_to_poly(child, program_vars))
            return result
        if kind == z3.Z3_OP_POWER:
            base, exponent = expr.children()
            if not z3.is_int_value(exponent) or exponent.as_long() < 0:
                raise ValueError(f"Unsupported polynomial power: {expr}")
            result = _const_poly(_one(), arity)
            base_poly = self._expr_to_poly(base, program_vars)
            for _ in range(exponent.as_long()):
                result = _mul_poly(result, base_poly)
            return result

        raise ValueError(f"Unsupported polynomial expression: {expr}")

    def _monomial_expr(self, degree: Degree, program_vars: Sequence[z3.ArithRef]):
        factors: List[z3.ArithRef] = []
        for var, power in zip(program_vars, degree):
            factors.extend([var] * power)
        return z3.Product(factors) if factors else _one()

    def _sum_of_squares(
        self, program_vars: Sequence[z3.ArithRef]
    ) -> Tuple[z3.ArithRef, List[z3.BoolRef]]:
        basis = self._monomial_degrees(len(program_vars), self.max_degree // 2)
        monomials = [self._monomial_expr(degree, program_vars) for degree in basis]
        dim = len(monomials)
        lower: List[List[z3.ArithRef]] = [
            [_zero() for _ in range(dim)] for _ in range(dim)
        ]
        constraints: List[z3.BoolRef] = []

        for row in range(dim):
            for col in range(row + 1):
                lower[row][col] = self._fresh_real(f"l_{row}_{col}")
            constraints.append(lower[row][row] >= 0)

        square_terms: List[z3.ArithRef] = []
        for col in range(dim):
            linear_terms = [
                lower[row][col] * monomials[row] for row in range(col, dim)
            ]
            square_terms.append(z3.Sum(linear_terms) * z3.Sum(linear_terms))

        return z3.Sum(square_terms), constraints

    def _coefficient_equalities(
        self,
        lhs: z3.ArithRef,
        rhs: z3.ArithRef,
        program_vars: Sequence[z3.ArithRef],
    ) -> List[z3.BoolRef]:
        lhs_poly = self._expr_to_poly(lhs, program_vars)
        rhs_poly = self._expr_to_poly(rhs, program_vars)
        degrees = set(lhs_poly).union(rhs_poly)
        return [
            lhs_poly.get(degree, _zero()) == rhs_poly.get(degree, _zero())
            for degree in degrees
        ]

    def apply_entailment_symbolic(
        self,
        conclusion: z3.BoolRef,
        program_vars: Sequence[z3.ArithRef],
    ) -> List[z3.BoolRef]:
        premise_polys: List[Tuple[z3.ArithRef, bool]] = []
        for constraint in self._constraints:
            premise_polys.extend(self._as_ge_zero(constraint))

        result: List[z3.BoolRef] = []
        for rhs_poly, rhs_strict in self._as_ge_zero(conclusion):
            poly_sum, sos_constraints = self._sum_of_squares(program_vars)
            result.extend(sos_constraints)

            strict_poly = _zero()
            if rhs_strict:
                strict_var = self._fresh_real("strict")
                result.append(strict_var >= 0)
                strict_poly = strict_poly + strict_var
                poly_sum = poly_sum + strict_var

            for premise_poly, premise_strict in premise_polys:
                sos_poly, more_constraints = self._sum_of_squares(program_vars)
                result.extend(more_constraints)
                if rhs_strict and premise_strict:
                    strict_var = self._fresh_real("strict")
                    result.append(strict_var >= 0)
                    strict_poly = strict_poly + strict_var
                    sos_poly = sos_poly + strict_var
                poly_sum = poly_sum + sos_poly * premise_poly

            if rhs_strict:
                result.append(strict_poly > 0)

            result.extend(
                self._coefficient_equalities(poly_sum, rhs_poly, program_vars)
            )

        return result
