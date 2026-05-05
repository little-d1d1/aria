"""
Use linear programming solvers for Optimization Modulo Theory problems.

This module provides two approaches:
1. Directly calling a disjunctive LP/ILP solver for convex problems
2. Iteratively calling LP/ILP solvers after splitting non-convex formulas

The LP conversion code in this file intentionally targets linear arithmetic
constraints and objectives only.
"""

from fractions import Fraction
from typing import Dict, List, Optional, Tuple

import pulp  # For LP solving
import z3


def arith_opt_with_lp(
    fml: z3.ExprRef, obj: z3.ExprRef, minimize: bool = True, solver_name: str = "pulp"
) -> Tuple[Optional[float], Optional[Dict[str, float]]]:
    """
    Solve an arithmetic optimization problem using linear programming.

    Args:
        fml: Z3 formula representing constraints
        obj: Z3 expression representing the objective function
        minimize: If True, minimize the objective; if False, maximize
        solver_name: Name of the LP solver to use ('pulp', 'gurobi', etc.)

    Returns:
        Tuple of (optimal value, model) if solution exists, (None, None) if unsatisfiable
    """
    # Method 1: Direct disjunctive LP solving
    if _is_convex_problem(fml):
        return _solve_direct_lp(fml, obj, minimize, solver_name)

    # Method 2: Iterative LP solving via DNF conversion
    return _solve_iterative_lp(fml, obj, minimize, solver_name)


def _is_convex_problem(fml: z3.ExprRef) -> bool:
    """Check if the formula represents a convex optimization problem."""
    # Analyze formula structure to detect convexity
    # - Linear constraints are convex
    # - Conjunction of convex constraints is convex
    # - Disjunctions make the problem non-convex
    visitor = ConvexityChecker()
    return visitor.check(fml)


def _solve_direct_lp(
    fml: z3.ExprRef, obj: z3.ExprRef, minimize: bool, solver_name: str
) -> Tuple[Optional[float], Optional[Dict[str, float]]]:
    """Solve convex problem directly using LP solver."""
    # Convert Z3 formula to LP format
    lp_prob = pulp.LpProblem("OMT", pulp.LpMinimize if minimize else pulp.LpMaximize)

    # Extract variables and constraints
    vars_map = _extract_variables(fml, obj)
    constraints = _convert_to_lp_constraints(fml, vars_map)
    objective = _convert_to_lp_objective(obj, vars_map)

    # Add constraints and objective to LP problem
    lp_prob += objective
    for constraint in constraints:
        lp_prob += constraint

    # Solve using specified solver
    if solver_name.lower() == "pulp":
        lp_prob.solve()
    elif solver_name.lower() == "gurobi":
        lp_prob.solve(pulp.GUROBI())

    # Extract solution
    if pulp.LpStatus[lp_prob.status] == "Optimal":
        value = float(pulp.value(lp_prob.objective))
        model: Dict[str, float] = {
            var.name: float(var.value()) for var in lp_prob.variables()
        }
        return value, model
    return None, None


def _solve_iterative_lp(
    fml: z3.ExprRef, obj: z3.ExprRef, minimize: bool, solver_name: str
) -> Tuple[Optional[float], Optional[Dict[str, float]]]:
    """Solve non-convex problem by converting to DNF and solving multiple LPs."""
    # Convert formula to DNF
    dnf_clauses = _convert_to_dnf(fml)

    best_value = float("inf") if minimize else float("-inf")
    best_model = None

    # Solve LP for each disjunct
    for clause in dnf_clauses:
        value, model = _solve_direct_lp(clause, obj, minimize, solver_name)
        if value is not None:
            if (minimize and value < best_value) or (
                not minimize and value > best_value
            ):
                best_value = value
                best_model = model

    return (best_value, best_model) if best_model is not None else (None, None)


def _is_linear_term(expr: z3.ExprRef) -> bool:
    """Check if an expression is linear (constant or variable or linear combination)."""
    if z3.is_const(expr) or z3.is_int_value(expr) or z3.is_rational_value(expr):
        return True

    if z3.is_mul(expr):
        # For multiplication, at most one term can be a variable
        var_count = 0
        for arg in expr.children():
            if not (z3.is_int_value(arg) or z3.is_rational_value(arg)):
                var_count += 1
            if var_count > 1:
                return False
        return True

    if z3.is_add(expr):
        # For addition, all terms must be linear
        return all(_is_linear_term(arg) for arg in expr.children())

    return False


class ConvexityChecker:
    """Visitor class to check formula convexity."""

    def check(self, expr: z3.ExprRef) -> bool:
        """
        Check if a Z3 expression represents a convex optimization problem.

        Args:
            expr: Z3 expression to check

        Returns:
            True if the expression represents a convex problem, False otherwise
        """
        if z3.is_and(expr):
            return all(self.check(arg) for arg in expr.children())
        if z3.is_or(expr):
            return False  # Disjunctions make problem non-convex

        # Handle comparison operators
        if (
            z3.is_eq(expr)
            or z3.is_le(expr)
            or z3.is_lt(expr)
            or z3.is_ge(expr)
            or z3.is_gt(expr)
        ):
            # Check if both sides of comparison are linear
            return all(_is_linear_term(arg) for arg in expr.children())

        return False


def _extract_variables(
    fml: z3.ExprRef, obj: z3.ExprRef
) -> Dict[z3.ExprRef, pulp.LpVariable]:
    """Extract variables from formula and objective, create LP variables."""
    vars_set = set()

    def collect_vars(expr):
        if z3.is_int_value(expr) or z3.is_rational_value(expr) or z3.is_bool(expr):
            return
        if z3.is_const(expr):
            vars_set.add(expr)
        else:
            for child in expr.children():
                collect_vars(child)

    collect_vars(fml)
    collect_vars(obj)

    return {
        var: pulp.LpVariable(
            str(var),
            cat=pulp.LpInteger if z3.is_int(var) else pulp.LpContinuous,
        )
        for var in vars_set
        if z3.is_int(var) or z3.is_real(var)
    }


def _z3_num_to_float(expr: z3.ExprRef) -> float:
    """Convert a Z3 numeric literal to a Python float."""
    if z3.is_int_value(expr):
        return float(expr.as_long())
    if z3.is_rational_value(expr):
        frac = Fraction(expr.numerator_as_long(), expr.denominator_as_long())
        return float(frac)
    raise TypeError(f"Expected numeric literal, got: {expr}")


def _linear_expr_to_lp(
    expr: z3.ExprRef,
    vars_map: Dict[z3.ExprRef, pulp.LpVariable],
) -> pulp.LpAffineExpression:
    """Convert a linear Z3 arithmetic expression into a PuLP affine expression."""
    if z3.is_int_value(expr) or z3.is_rational_value(expr):
        return pulp.LpAffineExpression(constant=_z3_num_to_float(expr))

    if z3.is_const(expr) and expr in vars_map:
        return pulp.LpAffineExpression([(vars_map[expr], 1.0)])

    if z3.is_add(expr):
        total = pulp.LpAffineExpression()
        for child in expr.children():
            total += _linear_expr_to_lp(child, vars_map)
        return total

    if z3.is_mul(expr):
        coeff = 1.0
        symbolic_terms: List[z3.ExprRef] = []
        for child in expr.children():
            if z3.is_int_value(child) or z3.is_rational_value(child):
                coeff *= _z3_num_to_float(child)
            else:
                symbolic_terms.append(child)

        if not symbolic_terms:
            return pulp.LpAffineExpression(constant=coeff)
        if len(symbolic_terms) != 1:
            raise ValueError(f"Non-linear multiplication is not supported: {expr}")
        return coeff * _linear_expr_to_lp(symbolic_terms[0], vars_map)

    if expr.decl().kind() == z3.Z3_OP_UMINUS:
        return -_linear_expr_to_lp(expr.children()[0], vars_map)

    raise ValueError(f"Unsupported arithmetic expression for LP conversion: {expr}")


def _convert_to_lp_constraints(
    fml: z3.ExprRef, vars_map: Dict[z3.ExprRef, pulp.LpVariable]
) -> List[pulp.LpConstraint]:
    """
    Convert Z3 formula to LP constraints.

    Args:
        fml: Z3 formula to convert
        vars_map: Mapping from Z3 variables to PuLP variables

    Returns:
        List of LP constraints

    """
    if z3.is_and(fml):
        constraints: List[pulp.LpConstraint] = []
        for child in fml.children():
            constraints.extend(_convert_to_lp_constraints(child, vars_map))
        return constraints

    if z3.is_true(fml):
        return []

    lhs, rhs = fml.children()
    lhs_lp = _linear_expr_to_lp(lhs, vars_map)
    rhs_lp = _linear_expr_to_lp(rhs, vars_map)

    if z3.is_eq(fml):
        return [lhs_lp == rhs_lp]
    if z3.is_le(fml):
        return [lhs_lp <= rhs_lp]
    if z3.is_ge(fml):
        return [lhs_lp >= rhs_lp]
    if z3.is_lt(fml):
        return [lhs_lp <= rhs_lp]
    if z3.is_gt(fml):
        return [lhs_lp >= rhs_lp]

    raise ValueError(f"Unsupported formula shape for LP conversion: {fml}")


def _convert_to_lp_objective(
    obj: z3.ExprRef, vars_map: Dict[z3.ExprRef, pulp.LpVariable]
) -> pulp.LpAffineExpression:
    """
    Convert Z3 objective expression to LP objective.

    Args:
        obj: Z3 expression representing the objective function
        vars_map: Mapping from Z3 variables to PuLP variables

    Returns:
        PuLP affine expression representing the objective

    """
    return _linear_expr_to_lp(obj, vars_map)


def _convert_to_dnf(fml: z3.ExprRef) -> List[z3.ExprRef]:
    """Convert formula to Disjunctive Normal Form."""
    # Use Z3's tactics to transform the formula
    tactic = z3.Then(
        z3.Tactic("simplify"),
        z3.Tactic("elim-and"),
        z3.Tactic("tseitin-cnf"),
        z3.Tactic("split-clause"),
    )

    # Apply the tactic
    result = tactic(fml)

    # Convert the result into a list of disjuncts
    dnf_clauses = []
    for subgoal in result:
        conjunction = z3.And(list(subgoal))
        dnf_clauses.append(conjunction)

    return dnf_clauses
