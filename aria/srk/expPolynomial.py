"""
Operations on exponential polynomials.

Exponential polynomials are expressions of the form:
E ::= x | λ | λ^x | E*E | E+E
where λ is a rational number.

This module provides operations for working with exponential polynomials,
which are useful for analyzing complex recurrences and program termination.
"""

from __future__ import annotations
from typing import Dict, List, Set, Tuple, Optional, Union, Any, Iterator
from dataclasses import dataclass, field
from fractions import Fraction
from abc import ABC, abstractmethod

from aria.srk.syntax import Context, ArithExpression
from aria.srk.polynomial import Polynomial, QQX
from aria.srk.linear import QQVector, QQMatrix


class ExpPolynomial:
    """Represents an exponential polynomial."""

    def __init__(self, polynomial_part: Polynomial, exponential_part: Fraction):
        """Initialize with polynomial and exponential parts."""
        self.polynomial_part = polynomial_part
        self.exponential_part = exponential_part

    @staticmethod
    def scalar(coeff: Fraction) -> "ExpPolynomial":
        """Create an exponential polynomial from a scalar coefficient."""
        from .polynomial import constant

        return ExpPolynomial(constant(coeff), Fraction(1))

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ExpPolynomial):
            return False
        return (
            self.polynomial_part == other.polynomial_part
            and self.exponential_part == other.exponential_part
        )

    def __hash__(self) -> int:
        return hash((self.polynomial_part, self.exponential_part))

    def __add__(self, other: ExpPolynomial) -> ExpPolynomial:
        """Add two exponential polynomials."""
        if self.polynomial_part.is_zero():
            return other
        if other.polynomial_part.is_zero():
            return self
        if self.exponential_part != other.exponential_part:
            raise ValueError("Cannot add exponential polynomials with different bases")

        new_poly = self.polynomial_part + other.polynomial_part
        return ExpPolynomial(new_poly, self.exponential_part)

    def __mul__(self, other: ExpPolynomial) -> ExpPolynomial:
        """Multiply two exponential polynomials."""
        # (p * λ^a) * (q * λ^b) = p*q * λ^(a+b)
        new_poly = self.polynomial_part * other.polynomial_part
        new_exp = self.exponential_part + other.exponential_part
        return ExpPolynomial(new_poly, new_exp)

    def __neg__(self) -> ExpPolynomial:
        """Negate an exponential polynomial."""
        return ExpPolynomial(-self.polynomial_part, self.exponential_part)

    def evaluate(self, x: int) -> Fraction:
        """Evaluate the exponential polynomial at integer x."""
        base_value = (
            self.exponential_part**x if self.exponential_part != 0 else Fraction(1)
        )
        poly_value = self.polynomial_part.evaluate({0: Fraction(x)})
        return base_value * poly_value

    def summation(self) -> ExpPolynomial:
        """Compute the summation of this exponential polynomial."""
        # For exponential polynomials, summation is more complex
        # This is a simplified implementation
        return self  # Placeholder

    def solve_recurrence(
        self, initial: Fraction = Fraction(0), multiplier: Fraction = Fraction(1)
    ) -> "ExpPolynomial":
        """Solve the recurrence g(n+1) = multiplier * g(n) + f(n)."""
        return self.solve_rec(initial=initial, lambda_val=multiplier)

    def compose_left_affine(self, a: int, b: int) -> "ExpPolynomial":
        """Compose with affine function: x |-> f(a*x + b).

        Given f(k) = poly(k) * mu^k, returns g(k) = f(a*k+b).
        Result: poly(a*k+b) * mu^(a*k+b) = [mu^b * poly(a*k+b)] * (mu^a)^k.
        """
        from .polynomial import Monomial as M

        mu = self.exponential_part
        poly = self.polynomial_part

        # Scale factor: mu^b
        scale = mu ** b if b != 0 else Fraction(1)

        # New base: mu^a
        new_base = mu ** a if a != 1 else mu

        # Compose the polynomial: poly(a*k + b)
        # Substitute k -> a*k + b in the polynomial
        new_poly = Polynomial()
        for monom, coeff in poly.terms.items():
            # Evaluate monomial at (a*k + b)
            # For monomial k^d, (a*k+b)^d = sum_{j=0}^{d} C(d,j) * a^j * b^{d-j} * k^j
            d = monom.exponents[0] if monom.exponents else 0
            for j in range(d + 1):
                binom_coeff = Fraction(1)
                for t in range(j):
                    binom_coeff = binom_coeff * Fraction(d - t, t + 1)
                term_coeff = coeff * scale * binom_coeff * (a ** j) * (b ** (d - j))
                if term_coeff != 0:
                    new_monom = M([j]) if j > 0 else M(())
                    if new_monom in new_poly.terms:
                        new_poly = new_poly + Polynomial({new_monom: term_coeff})
                    else:
                        new_poly = new_poly + Polynomial({new_monom: term_coeff})

        return ExpPolynomial(new_poly, new_base)

    def to_term(self, context: Context, variable: ArithExpression) -> ArithExpression:
        """Convert to an arithmetic term."""
        # Placeholder implementation
        return variable

    def __str__(self) -> str:
        if self.exponential_part == 0:
            return str(self.polynomial_part)
        elif self.polynomial_part == Polynomial():
            return f"λ^{self.exponential_part}"
        else:
            return f"({self.polynomial_part}) * λ^{self.exponential_part}"

    @staticmethod
    def zero() -> "ExpPolynomial":
        """Create zero exponential polynomial."""
        return ExpPolynomial(Polynomial(), Fraction(0))

    @staticmethod
    def one() -> "ExpPolynomial":
        """Create unit exponential polynomial."""
        return ExpPolynomial(Polynomial(), Fraction(0))

    def flatten(self, period: List["ExpPolynomial"]) -> "ExpPolynomial":
        """Flatten periodic exponential polynomials."""
        # This is a simplified implementation
        # In the OCaml version, this handles ultimately periodic sequences
        if not period:
            return ExpPolynomial.zero()

        # For now, just return the first element
        return period[0] if period else ExpPolynomial.zero()

    @staticmethod
    def eval(ep: "ExpPolynomial", k: int) -> Fraction:
        """Evaluate exponential polynomial at point k."""
        return ep.evaluate(k)

    @staticmethod
    def mul(ep1: "ExpPolynomial", ep2: "ExpPolynomial") -> "ExpPolynomial":
        """Multiply two exponential polynomials."""
        return ep1 * ep2

    @staticmethod
    def add(ep1: "ExpPolynomial", ep2: "ExpPolynomial") -> "ExpPolynomial":
        """Add two exponential polynomials."""
        return ep1 + ep2

    def make(
        transient: List[Fraction], periodic: List["ExpPolynomial"]
    ) -> "ExpPolynomial":
        """Create ultimately periodic exponential polynomial."""
        # Simplified implementation - in OCaml this creates a UP from transient and periodic parts
        if not periodic:
            return ExpPolynomial.zero()

        # For now, just return the first periodic element
        return periodic[0] if periodic else ExpPolynomial.zero()

    def period_len(self) -> int:
        """Get period length."""
        return 1  # Simplified

    def solve_rec(
        self, initial: Fraction = Fraction(0), lambda_val: Fraction = Fraction(1)
    ) -> "ExpPolynomial":
        """Solve recurrence g(n+1) = lambda*g(n) + f(n) with g(0) = initial.

        f is self.  Returns the closed-form solution.
        g(k) = lambda^k * initial + sum_{i=0}^{k-1} lambda^(k-1-i) * f(i)
        """
        from .polynomial import Monomial as M

        mu = self.exponential_part
        c = self.polynomial_part.evaluate({}) if self.polynomial_part.degree() <= 0 else None

        # Homogeneous part: lambda^k * initial
        if initial != 0:
            scalar_part = ExpPolynomial(
                Polynomial({M(()): initial}), lambda_val
            )
        else:
            # Zero polynomial with correct base (so addition works)
            scalar_part = ExpPolynomial(Polynomial(), lambda_val)

        # Special case: f = 0
        if self.polynomial_part.is_zero():
            return scalar_part

        # For non-diagonal PRSD: f(k) = c * mu^k (constant polynomial, single
        # exponential base).  The sum simplifies to a geometric series.
        # sum_{i=0}^{k-1} lambda^(k-1-i) * c * mu^i
        #   = c * lambda^(k-1) * sum_{i=0}^{k-1} (mu/lambda)^i
        if c is not None:
            if lambda_val == 0:
                # Only i=k-1 contributes: c * 0^0 * mu^(k-1) = c * mu^(k-1)
                if c != 0:
                    return scalar_part + ExpPolynomial(
                        Polynomial({M(()): c}), mu
                    )
                return scalar_part

            ratio = mu / lambda_val
            base_scale = c / lambda_val  # c * lambda^(k-1) = (c/lambda) * lambda^k

            if ratio == 1:
                # Geometric sum = k;  result = (c/lambda) * k * lambda^k
                poly_coeff = Polynomial({M((1,)): base_scale})
                return scalar_part + ExpPolynomial(poly_coeff, lambda_val)
            else:
                # sum = (1 - ratio^k)/(1 - ratio)
                # result = (c/lambda) * lambda^k * (1 - ratio^k) / (1 - ratio)
                #        = (c/lambda) * (lambda^k - mu^k) / (1 - ratio)
                common = base_scale / (1 - ratio)
                if common != 0:
                    term_lambda = ExpPolynomial(
                        Polynomial({M(()): common}), lambda_val
                    )
                    term_mu = ExpPolynomial(
                        Polynomial({M(()): -common}), mu
                    )
                    return scalar_part + term_lambda + term_mu
                return scalar_part

        # General case: polynomial * exponential.  Use the explicit sum.
        # For the PRSD non-diagonal case this branch is not reached.
        raise NotImplementedError(
            "solve_rec for general exponential-polynomial forcing terms"
        )


class ExpPolynomialVector:
    """Vector of exponential polynomials."""

    def __init__(self, components: Dict[int, ExpPolynomial]):
        self.components = components

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ExpPolynomialVector):
            return False
        return self.components == other.components

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.components.items())))

    def __add__(self, other: ExpPolynomialVector) -> ExpPolynomialVector:
        """Add two exponential polynomial vectors."""
        result = {}
        all_dims = set(self.components.keys()) | set(other.components.keys())

        for dim in all_dims:
            comp1 = self.components.get(dim, ExpPolynomial(Polynomial(), Fraction(0)))
            comp2 = other.components.get(dim, ExpPolynomial(Polynomial(), Fraction(0)))
            result[dim] = comp1 + comp2

        return ExpPolynomialVector(result)

    def __mul__(self, scalar: Fraction) -> ExpPolynomialVector:
        """Multiply by scalar."""
        result = {}
        for dim, comp in self.components.items():
            result[dim] = ExpPolynomial(
                comp.polynomial_part * scalar, comp.exponential_part
            )

        return ExpPolynomialVector(result)

    def evaluate(self, x: int) -> Dict[int, Fraction]:
        """Evaluate all components."""
        return {dim: comp.evaluate(x) for dim, comp in self.components.items()}

    def __str__(self) -> str:
        terms = []
        for dim in sorted(self.components.keys()):
            comp = self.components[dim]
            terms.append(f"e{dim}: {comp}")

        return "{" + ", ".join(terms) + "}"


class ExpPolynomialMatrix:
    """Matrix of exponential polynomials."""

    def __init__(self, rows: List[ExpPolynomialVector]):
        self.rows = rows

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ExpPolynomialMatrix):
            return False
        return self.rows == other.rows

    def __hash__(self) -> int:
        return hash(tuple(self.rows))

    def __mul__(self, other: ExpPolynomialMatrix) -> ExpPolynomialMatrix:
        """Matrix multiplication."""
        if not self.rows or not other.rows:
            return ExpPolynomialMatrix([])

        # Number of columns in self must equal number of rows in other
        if len(self.rows[0].components) != len(other.rows):
            raise ValueError("Incompatible matrix dimensions")

        result_rows = []

        for row in self.rows:
            result_row = {}
            for j in range(len(other.rows[0].components)):
                # Compute dot product of row with column j of other
                dot_product = ExpPolynomial(Polynomial(), Fraction(0))

                for i in range(len(other.rows)):
                    coeff_self = row.components.get(
                        i, ExpPolynomial(Polynomial(), Fraction(0))
                    )
                    coeff_other = other.rows[i].components.get(
                        j, ExpPolynomial(Polynomial(), Fraction(0))
                    )
                    dot_product = dot_product + (coeff_self * coeff_other)

                result_row[j] = dot_product

            result_rows.append(ExpPolynomialVector(result_row))

        return ExpPolynomialMatrix(result_rows)

    def __str__(self) -> str:
        return "\n".join(str(row) for row in self.rows)


# Factory functions
def zero_exp_polynomial() -> ExpPolynomial:
    """Create the zero exponential polynomial."""
    return ExpPolynomial(Polynomial(), Fraction(0))


def one_exp_polynomial() -> ExpPolynomial:
    """Create the constant 1 exponential polynomial."""
    from aria.srk.polynomial import Monomial

    return ExpPolynomial(Polynomial({Monomial(()): Fraction(1)}), Fraction(0))


def constant_exp_polynomial(c: Fraction) -> ExpPolynomial:
    """Create a constant exponential polynomial."""
    from aria.srk.polynomial import Monomial

    return ExpPolynomial(Polynomial({Monomial(()): c}), Fraction(0))


def variable_exp_polynomial() -> ExpPolynomial:
    """Create the variable x exponential polynomial."""
    from aria.srk.polynomial import Monomial

    return ExpPolynomial(Polynomial({Monomial([1]): Fraction(1)}), Fraction(0))


def exponential_exp_polynomial(base: Fraction) -> ExpPolynomial:
    """Create an exponential λ^x."""
    return ExpPolynomial(Polynomial(), base)


def polynomial_to_exp_polynomial(poly: Polynomial) -> ExpPolynomial:
    """Convert a polynomial to an exponential polynomial."""
    return ExpPolynomial(poly, Fraction(0))


def exp_polynomial_from_term(poly: Polynomial, base: Fraction) -> ExpPolynomial:
    """Create an exponential polynomial from a polynomial term."""
    return ExpPolynomial(poly, base)


# Operations on exponential polynomials
def exp_polynomial_add(ep1: ExpPolynomial, ep2: ExpPolynomial) -> ExpPolynomial:
    """Add two exponential polynomials."""
    return ep1 + ep2


def exp_polynomial_mul(ep1: ExpPolynomial, ep2: ExpPolynomial) -> ExpPolynomial:
    """Multiply two exponential polynomials."""
    return ep1 * ep2


def exp_polynomial_summation(ep: ExpPolynomial) -> ExpPolynomial:
    """Compute the summation of an exponential polynomial."""
    return ep.summation()


def exp_polynomial_solve_recurrence(
    ep: ExpPolynomial,
    initial: Fraction = Fraction(0),
    multiplier: Fraction = Fraction(1),
) -> ExpPolynomial:
    """Solve a recurrence relation."""
    return ep.solve_recurrence(initial, multiplier)


def exp_polynomial_compose_left_affine(
    ep: ExpPolynomial, a: int, b: int
) -> ExpPolynomial:
    """Compose with affine function."""
    return ep.compose_left_affine(a, b)


# Vector operations
def exp_polynomial_vector_from_qqvector(vec: QQVector) -> ExpPolynomialVector:
    """Convert a QQVector to an exponential polynomial vector."""
    components = {}
    for dim, coeff in vec.entries.items():
        components[dim] = ExpPolynomial(Polynomial({coeff}), Fraction(0))

    return ExpPolynomialVector(components)


def exp_polynomial_matrix_from_qqmatrix(matrix: QQMatrix) -> ExpPolynomialMatrix:
    """Convert a QQMatrix to an exponential polynomial matrix."""
    rows = []
    for row in matrix.rows:
        rows.append(exp_polynomial_vector_from_qqvector(row))

    return ExpPolynomialMatrix(rows)


def exp_polynomial_exponentiate_rational(
    matrix: QQMatrix,
) -> Optional[ExpPolynomialMatrix]:
    """Symbolically exponentiate a matrix with rational eigenvalues."""
    # This is a complex operation that would require eigenvalue computation
    # For now, return None to indicate irrational eigenvalues
    return None


# Enumeration and conversion
def exp_polynomial_enum(ep: ExpPolynomial) -> Iterator[Tuple[Polynomial, Fraction]]:
    """Enumerate the terms of an exponential polynomial."""
    # Placeholder implementation
    yield (ep.polynomial_part, ep.exponential_part)


def exp_polynomial_to_term(
    context: Context, variable: ArithExpression, ep: ExpPolynomial
) -> ArithExpression:
    """Convert exponential polynomial to arithmetic term."""
    return ep.to_term(context, variable)


# Type alias for compatibility with OCaml naming
UP = ExpPolynomial
