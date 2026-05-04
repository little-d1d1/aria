"""Shared floating-point OMT utilities."""

import itertools
from typing import Optional, Sequence, Tuple, cast

import z3

_FRESH_ID = itertools.count()


def fresh_fp_const(sort: z3.FPSortRef, prefix: str = "fp_obj") -> z3.ExprRef:
    """Create a fresh FP constant of the given sort."""
    return cast(z3.FPRef, z3.Const(f"__aria_{prefix}_{next(_FRESH_ID)}", sort))


def fp_value_from_bits(bits: int, sort: z3.FPSortRef) -> z3.ExprRef:
    """Construct an exact FP constant from its IEEE-754 bit pattern."""
    width = sort.ebits() + sort.sbits()
    return z3.fpBVToFP(z3.BitVecVal(bits, width), sort)


def fp_value_from_bits_expr(bits: z3.BitVecRef, sort: z3.FPSortRef) -> z3.ExprRef:
    """Construct an FP term from a bit-vector expression."""
    return z3.fpBVToFP(bits, sort)


def fp_model_value(model: z3.ModelRef, fp_expr: z3.ExprRef) -> z3.ExprRef:
    """Extract an exact FP value from a model, preserving NaN payload/sign."""
    bits = model.eval(z3.fpToIEEEBV(fp_expr), model_completion=True)
    return fp_value_from_bits(int(str(bits)), cast(z3.FPSortRef, fp_expr.sort()))


def fp_value_bits(value: z3.ExprRef) -> int:
    """Extract the exact IEEE-754 bit pattern from an exact FP value term."""
    if value.num_args() == 1:
        return int(str(value.arg(0)))

    probe = z3.FP("__aria_fp_bits_probe", cast(z3.FPSortRef, value.sort()))
    solver = z3.Solver()
    solver.add(z3.fpToIEEEBV(probe) == z3.fpToIEEEBV(value))
    if solver.check() != z3.sat:
        raise ValueError("Unable to extract floating-point bit pattern")
    return int(str(solver.model().eval(z3.fpToIEEEBV(probe), model_completion=True)))


def fp_order_key_bits(bits: int, sort: z3.FPSortRef) -> int:
    """Map a non-NaN IEEE bit-pattern to an unsigned key preserving numeric order."""
    width = sort.ebits() + sort.sbits()
    sign_mask = 1 << (width - 1)
    all_ones = (1 << width) - 1
    if bits & sign_mask:
        return all_ones ^ bits
    return bits ^ sign_mask


def fp_order_key_expr(bits: z3.BitVecRef) -> z3.BitVecRef:
    """Bit-vector expression version of :func:`fp_order_key_bits`."""
    width = bits.size()
    sign = z3.Extract(width - 1, width - 1, bits)
    sign_mask = z3.BitVecVal(1 << (width - 1), width)
    return cast(
        z3.BitVecRef,
        z3.If(sign == z3.BitVecVal(1, 1), ~bits, bits ^ sign_mask),
    )


def format_fp_value(value: z3.ExprRef) -> str:
    """Render an exact FP value with both readable and exact bit forms."""
    sort = cast(z3.FPSortRef, value.sort())
    width = sort.ebits() + sort.sbits()
    hex_width = (width + 3) // 4
    return f"{z3.simplify(value)} [bits=0x{fp_value_bits(value):0{hex_width}x}]"


def format_fp_values(values: Sequence[Optional[z3.ExprRef]]) -> str:
    """Render a list of exact FP values."""
    rendered = ["None" if value is None else format_fp_value(value) for value in values]
    return "[" + ", ".join(rendered) + "]"


def format_fp_frontier(frontier: Sequence[Sequence[z3.ExprRef]]) -> str:
    """Render a Pareto frontier of FP objective tuples."""
    rendered = [format_fp_values(point) for point in frontier]
    return "[" + ", ".join(rendered) + "]"


def prepare_fp_objective(
    z3_fml: z3.ExprRef, z3_obj: z3.ExprRef, prefix: str = "fp_obj"
) -> Tuple[z3.ExprRef, z3.ExprRef]:
    """Ensure the objective is represented by a named FP variable."""
    if z3_obj.sort_kind() != z3.Z3_FLOATING_POINT_SORT:
        raise ValueError("Expected a floating-point objective")

    if z3.is_const(z3_obj) and z3_obj.decl().arity() == 0:
        return z3_fml, z3_obj

    obj_var = fresh_fp_const(cast(z3.FPSortRef, z3_obj.sort()), prefix=prefix)
    return cast(z3.ExprRef, z3.And(z3_fml, obj_var == z3_obj)), obj_var


def prepare_fp_objective_with_bits(
    z3_fml: z3.ExprRef, z3_obj: z3.ExprRef, prefix: str = "fp_obj"
) -> Tuple[z3.ExprRef, z3.ExprRef, z3.BitVecRef]:
    """Ensure the objective has both named FP and IEEE-bit-vector views."""
    fml, obj_var = prepare_fp_objective(z3_fml, z3_obj, prefix=prefix)
    obj_sort = cast(z3.FPSortRef, obj_var.sort())
    width = obj_sort.ebits() + obj_sort.sbits()
    bits_var = z3.BitVec(f"__aria_{prefix}_bits_{next(_FRESH_ID)}", width)
    return (
        cast(z3.ExprRef, z3.And(fml, obj_var == fp_value_from_bits_expr(bits_var, obj_sort))),
        obj_var,
        bits_var,
    )


def pin_fp_value(fp_var: z3.ExprRef, value: z3.ExprRef) -> z3.ExprRef:
    """Constrain an FP term to an exact IEEE-754 value, preserving NaNs and zeros."""
    sort = cast(z3.FPSortRef, fp_var.sort())
    width = sort.ebits() + sort.sbits()
    return cast(
        z3.BoolRef,
        z3.fpToIEEEBV(fp_var) == z3.BitVecVal(fp_value_bits(value), width),
    )


def fp_is_nan_value(value: z3.ExprRef) -> bool:
    """Return whether an exact FP value is NaN."""
    return z3.is_true(z3.simplify(z3.fpIsNaN(value)))
