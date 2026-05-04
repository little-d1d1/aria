"""Engine-agnostic floating-point optimization composition helpers."""

from typing import List, Optional, Sequence, Tuple, cast

import z3

from aria.pyomt.omtfp.fp_opt_iterative_search import (
    fp_opt_with_binary_search,
    fp_opt_with_linear_search,
    fp_opt_with_ofpbs,
)
from aria.pyomt.omtfp.fp_opt_utils import (
    fp_is_nan_value,
    fp_model_value,
    pin_fp_value,
    prepare_fp_objective,
)


def fp_optimize_boxed(
    z3_fml: z3.ExprRef,
    objectives: Sequence[z3.ExprRef],
    directions: Sequence[str],
    engine: str,
    solver_name: str,
) -> List[Optional[z3.ExprRef]]:
    """Optimize each objective independently under boxed semantics."""
    results: List[Optional[z3.ExprRef]] = []
    for objective, direction in zip(objectives, directions):
        results.append(
            solve_fp_objective(
                z3_fml,
                objective,
                minimize=direction == "min",
                engine=engine,
                solver_name=solver_name,
            )
        )
    return results


def fp_optimize_lex(
    z3_fml: z3.ExprRef,
    objectives: Sequence[z3.ExprRef],
    directions: Sequence[str],
    engine: str,
    solver_name: str,
) -> List[Optional[z3.ExprRef]]:
    """Optimize objectives lexicographically under the paper semantics."""
    current_fml = z3_fml
    results: List[Optional[z3.ExprRef]] = []

    for index, (objective, direction) in enumerate(zip(objectives, directions)):
        current_fml, obj_var = prepare_fp_objective(
            current_fml, objective, prefix=f"lex_fp_obj_{index}"
        )
        result = solve_fp_objective(
            current_fml,
            obj_var,
            minimize=direction == "min",
            engine=engine,
            solver_name=solver_name,
        )
        results.append(result)
        if result is None:
            break
        current_fml = cast(z3.ExprRef, z3.And(current_fml, pin_fp_value(obj_var, result)))

    return results


def _normalize_fp_objectives(
    z3_fml: z3.ExprRef, objectives: Sequence[z3.ExprRef], prefix: str
) -> Tuple[z3.ExprRef, List[z3.ExprRef]]:
    """Convert all objectives into named FP variables over one formula."""
    current_fml = z3_fml
    obj_vars: List[z3.ExprRef] = []
    for index, objective in enumerate(objectives):
        current_fml, obj_var = prepare_fp_objective(
            current_fml, objective, prefix=f"{prefix}_{index}"
        )
        obj_vars.append(obj_var)
    return current_fml, obj_vars


def _fp_is_strictly_better(
    left: z3.ExprRef, right: z3.ExprRef, direction: str
) -> bool:
    """Check whether one exact FP value is strictly better than another."""
    if fp_is_nan_value(right):
        return not fp_is_nan_value(left)
    if fp_is_nan_value(left):
        return False
    if direction == "min":
        return z3.is_true(z3.simplify(z3.fpLT(left, right)))
    return z3.is_true(z3.simplify(z3.fpGT(left, right)))


def _fp_no_worse_constraint(
    obj_var: z3.ExprRef, value: z3.ExprRef, direction: str
) -> z3.ExprRef:
    """Constraint requiring an objective not to get worse than a reference."""
    if fp_is_nan_value(value):
        return z3.BoolVal(True)
    if direction == "min":
        return cast(
            z3.ExprRef,
            z3.And(z3.Not(z3.fpIsNaN(obj_var)), z3.fpLEQ(obj_var, value)),
        )
    return cast(
        z3.ExprRef,
        z3.And(z3.Not(z3.fpIsNaN(obj_var)), z3.fpGEQ(obj_var, value)),
    )


def _fp_strictly_better_constraint(
    obj_var: z3.ExprRef, value: z3.ExprRef, direction: str
) -> z3.ExprRef:
    """Constraint requiring an objective to improve over a reference."""
    if fp_is_nan_value(value):
        return cast(z3.ExprRef, z3.Not(z3.fpIsNaN(obj_var)))
    if direction == "min":
        return cast(
            z3.ExprRef,
            z3.And(z3.Not(z3.fpIsNaN(obj_var)), z3.fpLT(obj_var, value)),
        )
    return cast(
        z3.ExprRef,
        z3.And(z3.Not(z3.fpIsNaN(obj_var)), z3.fpGT(obj_var, value)),
    )


def _extract_fp_point(model: z3.ModelRef, obj_vars: Sequence[z3.ExprRef]) -> List[z3.ExprRef]:
    """Extract exact objective values from a model."""
    return [fp_model_value(model, obj_var) for obj_var in obj_vars]


def _find_point_with_objective_value(
    z3_fml: z3.ExprRef,
    obj_vars: Sequence[z3.ExprRef],
    objective_index: int,
    objective_value: z3.ExprRef,
) -> Optional[List[z3.ExprRef]]:
    """Find a witness point for a fixed objective value."""
    solver = z3.Solver()
    solver.add(z3_fml)
    solver.add(pin_fp_value(obj_vars[objective_index], objective_value))
    if solver.check() != z3.sat:
        return None
    return _extract_fp_point(solver.model(), obj_vars)


def _refine_fp_pareto_point(
    z3_fml: z3.ExprRef,
    obj_vars: Sequence[z3.ExprRef],
    directions: Sequence[str],
    initial_point: Sequence[z3.ExprRef],
    engine: str,
    solver_name: str,
) -> List[z3.ExprRef]:
    """Iteratively improve a feasible point until it becomes Pareto-optimal."""
    current = list(initial_point)

    improved = True
    while improved:
        improved = False
        for index, (obj_var, direction) in enumerate(zip(obj_vars, directions)):
            local_constraints = [z3_fml]
            for ref_var, ref_value, ref_dir in zip(obj_vars, current, directions):
                local_constraints.append(_fp_no_worse_constraint(ref_var, ref_value, ref_dir))

            local_fml = cast(z3.ExprRef, z3.And(*local_constraints))
            best_value = solve_fp_objective(
                local_fml,
                obj_var,
                minimize=direction == "min",
                engine=engine,
                solver_name=solver_name,
            )
            if best_value is None:
                continue

            witness_point = _find_point_with_objective_value(
                local_fml, obj_vars, index, best_value
            )
            if witness_point is None:
                continue

            if any(
                _fp_is_strictly_better(new_value, old_value, ref_dir)
                for new_value, old_value, ref_dir in zip(
                    witness_point, current, directions
                )
            ):
                current = witness_point
                improved = True

    return current


def fp_optimize_pareto(
    z3_fml: z3.ExprRef,
    objectives: Sequence[z3.ExprRef],
    directions: Sequence[str],
    engine: str,
    solver_name: str,
) -> List[List[z3.ExprRef]]:
    """Enumerate Pareto-optimal FP objective tuples under the paper semantics."""
    current_fml, obj_vars = _normalize_fp_objectives(
        z3_fml, objectives, prefix="pareto_fp_obj"
    )
    frontier: List[List[z3.ExprRef]] = []
    blocking_constraints: List[z3.ExprRef] = []

    while True:
        solver = z3.Solver()
        solver.add(current_fml)
        solver.add(*blocking_constraints)
        if solver.check() != z3.sat:
            break

        seed_point = _extract_fp_point(solver.model(), obj_vars)
        pareto_point = _refine_fp_pareto_point(
            cast(z3.ExprRef, z3.And(current_fml, *blocking_constraints)),
            obj_vars,
            directions,
            seed_point,
            engine,
            solver_name,
        )
        frontier.append(pareto_point)

        blocking_constraints.append(
            cast(
                z3.ExprRef,
                z3.Or(
                    *[
                        _fp_strictly_better_constraint(obj_var, value, direction)
                        for obj_var, value, direction in zip(
                            obj_vars, pareto_point, directions
                        )
                    ]
                ),
            )
        )

    return frontier


def solve_fp_objective(
    z3_fml: z3.ExprRef,
    z3_obj: z3.ExprRef,
    minimize: bool,
    engine: str,
    solver_name: str,
) -> Optional[z3.ExprRef]:
    """Dispatch single-objective OMT(QF_FP) solving."""
    if engine == "iter":
        search_type = solver_name.split("-")[-1]
        backend = solver_name.split("-")[0]
        if search_type == "ls":
            return fp_opt_with_linear_search(z3_fml, z3_obj, minimize, backend)
        if search_type == "bs":
            return fp_opt_with_binary_search(z3_fml, z3_obj, minimize, backend)
        if search_type == "ofpbs":
            return fp_opt_with_ofpbs(z3_fml, z3_obj, minimize, backend)
        raise ValueError(f"Unsupported FP iterative solver configuration: {solver_name}")
    if engine == "maxsat":
        raise ValueError("OMT(QF_FP) does not support MaxSAT reduction")
    if engine == "z3py":
        raise ValueError("z3 Optimize does not support floating-point objectives")
    raise ValueError(f"Unsupported FP optimization engine: {engine}")
