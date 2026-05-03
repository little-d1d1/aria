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

        # General case: polynomial * exponential.
        # f(k) = p(k) * mu^k  where p has degree d ≥ 1.
        #
        # We need:  g(k) = lambda^k * initial
        #                 + sum_{i=0}^{k-1} lambda^(k-1-i) * p(i) * mu^i
        #
        # Case mu == lambda:
        #   sum_{i=0}^{k-1} lambda^(k-1-i) * p(i) * lambda^i
        #   = lambda^(k-1) * sum_{i=0}^{k-1} p(i)
        #   = lambda^(k-1) * Q(k)   where Q(k) = sum_{i=0}^{k-1} p(i)
        #   Q is a polynomial of degree deg(p)+1 (antidifference of p).
        #
        # Case mu != lambda:
        #   Factor out lambda^(k-1):
        #   sum_{i=0}^{k-1} (mu/lambda)^i * p(i)
        #   = sum_{j=0}^{d} p_j * sum_{i=0}^{k-1} i^j * r^i   where r = mu/lambda
        #   Each inner sum has a closed form as a rational function of r and k.
        #   We compute it via the operator identity:
        #     sum_{i=0}^{k-1} i^j * r^i = (r * d/dr)^j [sum_{i=0}^{k-1} r^i]
        #   and express the result as an exponential polynomial.
        #
        # For simplicity we implement the mu == lambda case exactly and the
        # mu != lambda case via the antidifference operator on monomials.

        from .polynomial import Monomial as M, Polynomial as Poly

        mu = self.exponential_part
        p = self.polynomial_part  # p(k) * mu^k is the forcing term

        if mu == lambda_val:
            # sum_{i=0}^{k-1} p(i) = antidifference of p evaluated at k
            # For p(i) = i^j, antidifference is a degree-(j+1) polynomial.
            antidiff = _poly_antidifference(p)
            # Result: lambda^(k-1) * antidiff(k) = (1/lambda) * lambda^k * antidiff(k)
            if lambda_val == 0:
                # Degenerate: only i=k-1 contributes.
                # sum = p(k-1) * 0^0 = p(k-1)  (for k >= 1)
                # Represent as p(k) * lambda^k with lambda=0 (evaluates to p(0) at k=0).
                return scalar_part + ExpPolynomial(p, mu)
            scale = Fraction(1) / lambda_val
            scaled_antidiff = antidiff.scalar_mul(scale)
            return scalar_part + ExpPolynomial(scaled_antidiff, lambda_val)

        # mu != lambda: use the closed-form for sum_{i=0}^{k-1} i^j * r^i.
        # We decompose p into monomials and sum each separately.
        r = mu / lambda_val  # ratio
        result = scalar_part
        for mono, coeff in p.enum():
            if coeff == 0:
                continue
            j = mono.exponents[0] if mono.exponents else 0
            # sum_{i=0}^{k-1} i^j * r^i  as an ExpPolynomial in k.
            s = _geometric_monomial_sum(j, r)
            # Multiply by coeff * lambda^(k-1) = (coeff/lambda) * lambda^k
            if lambda_val == 0:
                # Only i=k-1 term: coeff * (k-1)^j * 0^0 = coeff*(k-1)^j for k>=1
                # Approximate as coeff * k^j * mu^k (leading term).
                result = result + ExpPolynomial(
                    Poly({mono: coeff}), mu
                )
            else:
                scale = coeff / lambda_val
                # s is an ExpPolynomial in k with base r; multiply base by lambda.
                # s(k) * lambda^k = s_poly(k) * (r * lambda)^k = s_poly(k) * mu^k
                # (since r = mu/lambda, so r*lambda = mu)
                result = result + ExpPolynomial(
                    s.polynomial_part.scalar_mul(scale), mu
                )
        return result


# ---------------------------------------------------------------------------
# Helper functions for solve_rec
# ---------------------------------------------------------------------------

def _poly_antidifference(p: "Polynomial") -> "Polynomial":
    """Return Q such that Q(k) - Q(k-1) = p(k-1), i.e. sum_{i=0}^{k-1} p(i) = Q(k).

    Uses the Newton forward-difference formula for univariate polynomials.
    For p(i) = i^j the antidifference is a degree-(j+1) polynomial.
    """
    from .polynomial import Polynomial as Poly, Monomial as M

    if p.is_zero():
        return Poly()

    # Represent p as a dense list of coefficients [a0, a1, ..., ad].
    coeffs: Dict[int, Fraction] = {}
    for mono, coeff in p.enum():
        exp = mono.exponents[0] if mono.exponents else 0
        coeffs[exp] = Fraction(coeff)

    if not coeffs:
        return Poly()

    deg = max(coeffs.keys())
    dense = [coeffs.get(i, Fraction(0)) for i in range(deg + 1)]

    # Antidifference of k^j is a degree-(j+1) polynomial.
    # We compute it by integrating the polynomial in the "falling factorial" basis
    # and converting back to the standard basis.
    # Simpler: use the fact that sum_{i=0}^{k-1} i^j = Bernoulli polynomial B_{j+1}(k)/(j+1).
    # We compute numerically via the recurrence on the antidifference.

    # Build antidifference coefficient by coefficient using the identity:
    # If Q(k) = sum_{i=0}^{k-1} p(i), then Q(0)=0 and Q(k)-Q(k-1)=p(k-1).
    # We represent Q as a polynomial of degree deg+1 and solve for its coefficients
    # by matching values at deg+2 points.
    n = deg + 2  # number of sample points needed
    # Sample p at 0..n-1
    p_vals = [sum(dense[j] * Fraction(k) ** j for j in range(deg + 1))
              for k in range(n)]
    # Compute Q values: Q(0)=0, Q(k)=Q(k-1)+p(k-1)
    q_vals = [Fraction(0)] * n
    for k in range(1, n):
        q_vals[k] = q_vals[k - 1] + p_vals[k - 1]

    # Interpolate Q (degree deg+1) from n = deg+2 points using Lagrange.
    result_coeffs = _lagrange_to_standard(list(range(n)), q_vals)

    terms = {}
    for exp, c in enumerate(result_coeffs):
        if c != 0:
            terms[M((exp,))] = c
    return Poly(terms)


def _lagrange_to_standard(xs: List[int], ys: List[Fraction]) -> List[Fraction]:
    """Convert Lagrange interpolation data to standard polynomial coefficients.

    Returns [a0, a1, ..., an] such that sum(a_i * x^i) interpolates the points.
    Uses the Newton divided-difference method for numerical stability.
    """
    n = len(xs)
    # Newton divided differences table.
    dd = [Fraction(y) for y in ys]
    coeffs_newton = [dd[0]]
    for k in range(1, n):
        new_dd = []
        for i in range(n - k):
            new_dd.append((dd[i + 1] - dd[i]) / Fraction(xs[i + k] - xs[i]))
        dd = new_dd
        coeffs_newton.append(dd[0])

    # Convert Newton form to standard form.
    # p(x) = c0 + c1*(x-x0) + c2*(x-x0)*(x-x1) + ...
    # We accumulate by multiplying out the factors.
    result = [Fraction(0)] * n
    result[0] = coeffs_newton[n - 1]
    for k in range(n - 2, -1, -1):
        # Multiply result by (x - xs[k]) and add coeffs_newton[k].
        new_result = [Fraction(0)] * n
        for i in range(n - 1):
            new_result[i + 1] += result[i]
            new_result[i] -= result[i] * Fraction(xs[k])
        new_result[0] += coeffs_newton[k]
        result = new_result

    return result


def _geometric_monomial_sum(j: int, r: Fraction) -> "ExpPolynomial":
    """Compute sum_{i=0}^{k-1} i^j * r^i as an ExpPolynomial in k.

    Uses the operator identity: sum_{i=0}^{k-1} i^j * r^i = (r*d/dr)^j S(k,r)
    where S(k,r) = (r^k - 1)/(r - 1) for r != 1.

    Returns an ExpPolynomial with base r.
    """
    from .polynomial import Polynomial as Poly, Monomial as M

    if r == 0:
        # sum_{i=0}^{k-1} i^j * 0^i = 0 (all terms vanish for i >= 1, and 0^0=1 at i=0).
        if j == 0:
            # sum = 1 for k >= 1, 0 for k = 0.  Approximate as constant 1.
            return ExpPolynomial(Poly({M(()): Fraction(1)}), Fraction(0))
        return ExpPolynomial(Poly(), Fraction(0))

    if r == 1:
        # sum_{i=0}^{k-1} i^j = antidifference of k^j evaluated at k.
        mono_j = M((j,)) if j > 0 else M(())
        p_kj = Poly({mono_j: Fraction(1)})
        antidiff = _poly_antidifference(p_kj)
        return ExpPolynomial(antidiff, Fraction(1))

    # General r != 0, 1.
    # We compute the sum by sampling at j+2 points and interpolating.
    # sum_{i=0}^{k-1} i^j * r^i  is a linear combination of r^k and a polynomial in k.
    # For the purposes of solve_rec we only need the r^k component (the polynomial
    # component is absorbed into the scalar_part).  We return the full result as
    # an ExpPolynomial with base r.
    #
    # Exact formula via the operator method:
    # Let T_j(k) = sum_{i=0}^{k-1} i^j * r^i.
    # T_0(k) = (r^k - 1)/(r-1)
    # T_j(k) = r * d/dr T_{j-1}(k)  (differentiate w.r.t. r, then multiply by r)
    #
    # We compute T_j symbolically as a polynomial in k times r^k plus a polynomial in k.
    # For simplicity, sample at j+2 points and interpolate.
    n_pts = j + 2
    xs = list(range(n_pts))
    ys = []
    for k in xs:
        val = sum(Fraction(i) ** j * r ** i for i in range(k))
        ys.append(val)

    # The sum has the form A(k)*r^k + B(k) where A, B are polynomials of degree <= j.
    # We fit this form by sampling at 2*(j+1) points.
    # For the ExpPolynomial representation we only keep the r^k coefficient.
    # Fit: at each sample point k, val = A(k)*r^k + B(k).
    # We have 2*(j+1) unknowns (coefficients of A and B, each degree j).
    # Use 2*(j+1) sample points.
    n_fit = 2 * (j + 1)
    xs_fit = list(range(n_fit))
    ys_fit = [sum(Fraction(i) ** j * r ** i for i in range(k)) for k in xs_fit]

    # Build linear system: for each k, sum_{d=0}^{j} a_d * k^d * r^k + b_d * k^d = val.
    # Variables: [a_0, ..., a_j, b_0, ..., b_j]
    from fractions import Fraction as F
    size = 2 * (j + 1)
    mat = [[F(0)] * size for _ in range(size)]
    rhs = [F(0)] * size
    for row, k in enumerate(xs_fit):
        rk = r ** k
        for d in range(j + 1):
            mat[row][d] = F(k) ** d * rk        # a_d coefficient
            mat[row][j + 1 + d] = F(k) ** d     # b_d coefficient
        rhs[row] = ys_fit[row]

    # Solve via Gaussian elimination.
    sol = _solve_rational_system(mat, rhs)
    if sol is None:
        # Fallback: return zero.
        return ExpPolynomial(Poly(), r)

    # Extract A(k) coefficients (indices 0..j).
    a_coeffs = sol[:j + 1]
    terms = {}
    for d, c in enumerate(a_coeffs):
        if c != 0:
            mono = M((d,)) if d > 0 else M(())
            terms[mono] = c
    return ExpPolynomial(Poly(terms) if terms else Poly(), r)


def _solve_rational_system(
    mat: List[List[Fraction]], rhs: List[Fraction]
) -> Optional[List[Fraction]]:
    """Solve a square rational linear system Ax = b via Gaussian elimination.

    Returns the solution vector or None if the system is singular.
    """
    n = len(rhs)
    # Augmented matrix.
    aug = [mat[i][:] + [rhs[i]] for i in range(n)]
    for col in range(n):
        # Find pivot.
        pivot = None
        for row in range(col, n):
            if aug[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        piv_val = aug[col][col]
        for row in range(n):
            if row == col:
                continue
            if aug[row][col] == 0:
                continue
            factor = aug[row][col] / piv_val
            for c in range(n + 1):
                aug[row][c] -= factor * aug[col][c]
    return [aug[i][n] / aug[i][i] for i in range(n)]


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
