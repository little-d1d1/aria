"""Dispatch tests for the OMT CLI solver entry points."""

import os
import tempfile

from aria.pyomt.omt_solver import solve_opt_file_result


def _write_tmp_smt2(contents: str) -> str:
    handle = tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False)
    try:
        handle.write(contents)
        return handle.name
    finally:
        handle.close()


def test_single_objective_integer_uses_theory_engine_override():
    filename = _write_tmp_smt2(
        """
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (assert (>= x 4))
        (assert (<= x 9))
        (minimize x)
        (check-sat)
        """
    )

    try:
        result = solve_opt_file_result(
            filename,
            engine="maxsat",
            solver_name="FM",
            int_engine="iter",
        )
    finally:
        os.unlink(filename)

    assert result.engine == "iter"
    assert result.value == 4


def test_multi_objective_integer_boxed_dispatches_arithmetic_backend():
    filename = _write_tmp_smt2(
        """
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (>= x 4))
        (assert (<= x 9))
        (assert (>= y 2))
        (assert (<= y 7))
        (minimize x)
        (maximize y)
        (check-sat)
        """
    )

    try:
        result = solve_opt_file_result(
            filename,
            engine="qsmt",
            solver_name="z3",
            opt_priority="box",
            int_engine="iter",
        )
    finally:
        os.unlink(filename)

    assert result.engine == "iter"
    assert result.value == [4, 7]


def test_multi_objective_bv_boxed_shuffle_still_returns_input_order():
    filename = _write_tmp_smt2(
        """
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 4))
        (declare-fun y () (_ BitVec 4))
        (assert (bvule x #x5))
        (assert (bvule y #x7))
        (maximize x)
        (minimize y)
        (check-sat)
        """
    )

    try:
        result = solve_opt_file_result(
            filename,
            engine="qsmt",
            solver_name="z3",
            opt_priority="box",
            bv_engine="iter",
            opt_box_shuffle=True,
            seed=13,
        )
    finally:
        os.unlink(filename)

    assert result.engine == "iter"
    assert result.value == [5, 0]
