"""Iterative OMT(QF_FP) search procedures."""

import logging
from typing import List, Optional, Sequence, cast

import z3

from aria.pyomt.omtfp.fp_opt_utils import (
    fp_model_value,
    fp_order_key_bits,
    fp_order_key_expr,
    fp_value_bits,
    fp_value_from_bits,
    prepare_fp_objective_with_bits,
)

logger = logging.getLogger(__name__)


def _bit_is_set(bits: int, width: int, index: int) -> int:
    return (bits >> (width - 1 - index)) & 1


def _bits_from_list(bits: Sequence[int]) -> int:
    value = 0
    for bit in bits:
        value = (value << 1) | bit
    return value


def _bit_constraint(bits_expr: z3.BitVecRef, index: int, value: int) -> z3.ExprRef:
    width = bits_expr.size()
    return z3.Extract(width - 1 - index, width - 1 - index, bits_expr) == z3.BitVecVal(
        value, 1
    )


class _DynamicAttractor:
    """Stateful implementation of the paper's dynamic attractor update."""

    def __init__(self, sort: z3.FPSortRef, minimize: bool) -> None:
        self.sort = sort
        self.minimize = minimize
        self.width = sort.ebits() + sort.sbits()
        self.ebits = sort.ebits()
        seed = z3.fpMinusInfinity(sort) if minimize else z3.fpPlusInfinity(sort)
        self._bits = fp_value_bits(seed)
        self._bits_list = [
            _bit_is_set(self._bits, self.width, index) for index in range(self.width)
        ]

    @property
    def bits(self) -> int:
        return self._bits

    def update(self, prefix_bits: Sequence[int]) -> int:
        if not prefix_bits:
            return self._bits

        k = len(prefix_bits) - 1
        self._bits_list[k] = 1 - self._bits_list[k]
        sign = prefix_bits[0]

        if self.minimize:
            if sign == 0:
                fill = 0
            elif k <= self.ebits:
                fill = 1
            else:
                fill = None
        else:
            if sign == 1:
                fill = 0
            elif k <= self.ebits:
                fill = 1
            else:
                fill = None

        if fill is not None:
            for index in range(k + 1, self.width):
                self._bits_list[index] = fill

        self._bits = _bits_from_list(self._bits_list)
        return self._bits


def _prepare_non_nan_problem(
    z3_fml: z3.ExprRef, obj_var: z3.ExprRef
) -> tuple[Optional[z3.ExprRef], Optional[z3.ModelRef]]:
    """Apply the paper's NaN rule and return the restricted non-NaN problem."""
    non_nan_solver = z3.Solver()
    non_nan_solver.add(z3_fml)
    non_nan_solver.add(z3.Not(z3.fpIsNaN(obj_var)))
    if non_nan_solver.check() == z3.sat:
        return (
            cast(z3.ExprRef, z3.And(z3_fml, z3.Not(z3.fpIsNaN(obj_var)))),
            non_nan_solver.model(),
        )

    base_solver = z3.Solver()
    base_solver.add(z3_fml)
    if base_solver.check() != z3.sat:
        return None, None
    return None, base_solver.model()


def _strictly_better_constraint(
    obj_var: z3.ExprRef, candidate: z3.ExprRef, minimize: bool
) -> z3.ExprRef:
    if minimize:
        return cast(z3.ExprRef, z3.fpLT(obj_var, candidate))
    return cast(z3.ExprRef, z3.fpGT(obj_var, candidate))


def _log_heuristic_limitation() -> None:
    logger.debug(
        "OFPBS enhancements for branching preference and bit-polarity updates are "
        "not applied because the z3 Python solver API does not expose equivalent "
        "per-bit controls."
    )


def fp_opt_with_linear_search(
    z3_fml: z3.ExprRef, z3_obj: z3.ExprRef, minimize: bool, solver_name: str = "z3"
) -> Optional[z3.ExprRef]:
    """Optimize a floating-point objective using strict iterative improvement."""
    if solver_name != "z3":
        raise ValueError("Floating-point OMT currently supports only the z3 backend")

    fml, obj_var, _ = prepare_fp_objective_with_bits(z3_fml, z3_obj, prefix="iter_fp_obj")
    base_solver = z3.Solver()
    base_solver.add(fml)
    if base_solver.check() != z3.sat:
        return None

    restricted_fml, model = _prepare_non_nan_problem(fml, obj_var)
    if restricted_fml is None:
        if model is None:
            return None
        return fp_model_value(model, obj_var)

    assert model is not None
    best = fp_model_value(model, obj_var)
    solver = z3.Solver()
    solver.add(restricted_fml)

    while True:
        solver.push()
        solver.add(_strictly_better_constraint(obj_var, best, minimize))
        if solver.check() != z3.sat:
            solver.pop()
            return best
        best = fp_model_value(solver.model(), obj_var)
        solver.pop()


def fp_opt_with_binary_search(
    z3_fml: z3.ExprRef, z3_obj: z3.ExprRef, minimize: bool, solver_name: str = "z3"
) -> Optional[z3.ExprRef]:
    """Optimize a floating-point objective by bisection over IEEE order keys."""
    if solver_name != "z3":
        raise ValueError("Floating-point OMT currently supports only the z3 backend")

    fml, obj_var, bits_var = prepare_fp_objective_with_bits(
        z3_fml, z3_obj, prefix="iter_fp_obj"
    )
    base_solver = z3.Solver()
    base_solver.add(fml)
    if base_solver.check() != z3.sat:
        return None

    restricted_fml, model = _prepare_non_nan_problem(fml, obj_var)
    if restricted_fml is None:
        if model is None:
            return None
        return fp_model_value(model, obj_var)

    assert model is not None
    sort = cast(z3.FPSortRef, obj_var.sort())
    key_expr = fp_order_key_expr(bits_var)
    low = fp_order_key_bits(fp_value_bits(z3.fpMinusInfinity(sort)), sort)
    high = fp_order_key_bits(fp_value_bits(z3.fpPlusInfinity(sort)), sort)
    best = fp_model_value(model, obj_var)
    best_key = fp_order_key_bits(fp_value_bits(best), sort)
    solver = z3.Solver()
    solver.add(restricted_fml)

    if minimize:
        upper = best_key
        lower = low
        while lower < upper:
            pivot = (lower + upper) // 2
            solver.push()
            solver.add(z3.ULE(key_expr, z3.BitVecVal(pivot, bits_var.size())))
            if solver.check() == z3.sat:
                best = fp_model_value(solver.model(), obj_var)
                best_key = fp_order_key_bits(fp_value_bits(best), sort)
                upper = best_key
            else:
                lower = pivot + 1
            solver.pop()
        return best

    lower = best_key
    upper = high
    while lower < upper:
        pivot = (lower + upper + 1) // 2
        solver.push()
        solver.add(z3.UGE(key_expr, z3.BitVecVal(pivot, bits_var.size())))
        if solver.check() == z3.sat:
            best = fp_model_value(solver.model(), obj_var)
            best_key = fp_order_key_bits(fp_value_bits(best), sort)
            lower = best_key
        else:
            upper = pivot - 1
        solver.pop()
    return best


def fp_opt_with_ofpbs(
    z3_fml: z3.ExprRef, z3_obj: z3.ExprRef, minimize: bool, solver_name: str = "z3"
) -> Optional[z3.ExprRef]:
    """Optimize a floating-point objective with the paper's OFPBS core search."""
    if solver_name != "z3":
        raise ValueError("Floating-point OMT currently supports only the z3 backend")

    _log_heuristic_limitation()
    fml, obj_var, bits_var = prepare_fp_objective_with_bits(
        z3_fml, z3_obj, prefix="iter_fp_obj"
    )
    base_solver = z3.Solver()
    base_solver.add(fml)
    if base_solver.check() != z3.sat:
        return None

    restricted_fml, initial_model = _prepare_non_nan_problem(fml, obj_var)
    if restricted_fml is None:
        if initial_model is None:
            return None
        result = fp_model_value(initial_model, obj_var)
        logger.info(
            "Iterative FP %simization result (NaN-only feasible space): %s",
            "min" if minimize else "max",
            result,
        )
        return result

    assert initial_model is not None
    sort = cast(z3.FPSortRef, obj_var.sort())
    width = sort.ebits() + sort.sbits()
    solver = z3.Solver()
    solver.add(restricted_fml)

    model = initial_model
    model_bits = int(str(model.eval(bits_var, model_completion=True)))
    prefix_bits: List[int] = []
    assumptions: List[z3.ExprRef] = []
    attractor = _DynamicAttractor(sort, minimize)

    for index in range(width):
        attractor_bit = _bit_is_set(attractor.bits, width, index)
        current_bit = _bit_is_set(model_bits, width, index)
        if current_bit == attractor_bit:
            prefix_bits.append(attractor_bit)
            assumptions.append(_bit_constraint(bits_var, index, attractor_bit))
            continue

        eq = _bit_constraint(bits_var, index, attractor_bit)
        if solver.check(*(assumptions + [eq])) == z3.sat:
            model = solver.model()
            model_bits = int(str(model.eval(bits_var, model_completion=True)))
            prefix_bits.append(attractor_bit)
            assumptions.append(eq)
            continue

        chosen_bit = 1 - attractor_bit
        prefix_bits.append(chosen_bit)
        assumptions.append(_bit_constraint(bits_var, index, chosen_bit))
        attractor.update(prefix_bits)

    result = fp_value_from_bits(
        int(str(model.eval(bits_var, model_completion=True))),
        sort,
    )
    logger.info(
        "Iterative FP %simization result: %s",
        "min" if minimize else "max",
        result,
    )
    return result
