"""Focused tests for BV helper modules and boxed wrappers."""

import multiprocessing as mp
import subprocess
import tempfile
from pathlib import Path

import z3
from pysmt.shortcuts import BV, Equals, Symbol
from pysmt.typing import BVType

from aria.pyomt import pysmt_utils
from aria.pyomt.omtbv import bv_opt_qsmt, bv_opt_utils
from aria.pyomt.omtbv import boxed as boxed_pkg
from aria.pyomt.omtbv.bit_blast_omt_solver import BitBlastOMTBVSolver
from aria.pyomt.omtbv.boxed import bv_boxed_compact, bv_boxed_obj_divide, bv_boxed_z3


def test_bv_qsmt_reduction_uses_bv_logic(monkeypatch):
    captured = {}

    def fake_solve_with_bin_smt(logic, qfml, obj_name, solver_name):
        captured["logic"] = logic
        captured["qfml"] = qfml
        captured["obj_name"] = obj_name
        return "sat\n((x #x09))"

    monkeypatch.setattr(bv_opt_qsmt, "solve_with_bin_smt", fake_solve_with_bin_smt)

    x = z3.BitVec("x", 4)
    result = bv_opt_qsmt.bv_opt_with_qsmt(z3.And(z3.UGT(x, 3), z3.ULT(x, 10)), x, minimize=False, solver_name="z3")

    assert result == "sat\n((x #x09))"
    assert captured["logic"] == "BV"
    assert captured["obj_name"] == "x"
    assert "ForAll" in str(captured["qfml"])


def test_bv_opt_utils_parsers_cover_common_formats(monkeypatch):
    assert bv_opt_utils.cnt([1, 0, 1]) == 5
    assert bv_opt_utils.list_to_int([[1, 0, 1], [1, 1]], [1, 0]) == [5, 0]
    assert bv_opt_utils.assum_in_m([1, -2], [1, 3, -2])

    cnf = "\n".join(
        [
            "p cnf 3 2",
            "1 -2 0",
            "3 0",
            "c 10 foo obj1 val:1] !1",
            "c 11 foo obj1 val:1] !2",
            "c 12 foo obj0 val:0] !3",
            "c 13 foo obj0 val:1] !4",
        ]
    )
    parsed = bv_opt_utils.read_cnf(cnf)
    assert parsed == ([[1, -2], [3]], [[10, 11], [12, 13]], [1, 0])

    z3_output = "\n".join(
        [
            "(objectives",
            "  (x 10)",
            ")",
            "(define-fun y () (_ BitVec 8)",
            "  #b00000101)",
        ]
    )
    assert bv_opt_utils.res_z3_trans(z3_output, objective_order=["y", "x"]) == [5, 10]

    monkeypatch.setattr(bv_opt_utils.global_config, "get_solver_path", lambda _name: None)
    monkeypatch.setattr(bv_opt_utils.shutil, "which", lambda name: "/usr/bin/z3" if name == "z3" else None)

    def fake_run(command, capture_output, text, check):
        assert command[0] == "/usr/bin/z3"
        assert command[-1] == "/tmp/example.smt2"
        return subprocess.CompletedProcess(command, 0, stdout="p cnf 0 0\n", stderr="")

    monkeypatch.setattr(bv_opt_utils.subprocess, "run", fake_run)
    assert bv_opt_utils.cnf_from_z3("/tmp/example.smt2") == "p cnf 0 0\n"


def test_boxed_package_exports_modules():
    assert boxed_pkg.bv_boxed_compact is bv_boxed_compact
    assert boxed_pkg.bv_boxed_obj_divide is bv_boxed_obj_divide
    assert boxed_pkg.bv_boxed_z3 is bv_boxed_z3


def test_boxed_z3_injects_get_objectives_and_parses_output(monkeypatch, tmp_path):
    smt2 = tmp_path / "boxed.smt2"
    smt2.write_text("(set-logic QF_BV)\n(get-model)\n", encoding="utf-8")
    seen = {}

    def fake_run(command, input, text, capture_output, check):
        seen["command"] = command
        seen["input"] = input
        return subprocess.CompletedProcess(command, 0, stdout="(objectives\n (x 5)\n)\n", stderr="")

    monkeypatch.setattr(bv_boxed_z3.subprocess, "run", fake_run)
    result = bv_boxed_z3.solve_boxed_z3(str(smt2), objective_order=["x"])

    assert result == [5]
    assert seen["command"] == ["z3", "opt.priority=box", "-in"]
    assert "(get-objectives)\n(get-model)" in seen["input"]


def test_boxed_obj_divide_helpers_cover_parsing_and_dispatch(monkeypatch):
    assert bv_boxed_obj_divide.parse_smt2_value_output("sat\n((x #x0a))") == 10
    assert bv_boxed_obj_divide.parse_smt2_value_output("sat\n((x #b0011))") == 3

    monkeypatch.setattr(bv_boxed_obj_divide, "bv_opt_with_qsmt", lambda *_args: "sat\n((obj_var #x07))")
    result_queue = mp.Queue()
    error_queue = mp.Queue()
    smt2 = """
    (declare-const x (_ BitVec 4))
    (declare-const obj_var (_ BitVec 4))
    (assert (bvule x #x7))
    (assert (= obj_var x))
    """
    bv_boxed_obj_divide.solve_objective(
        smt2,
        0,
        False,
        "qsmt",
        "z3",
        result_queue,
        error_queue,
    )
    result = result_queue.get(timeout=1)
    assert result.objective_id == 0
    assert result.value == 7
    assert result.status == bv_boxed_obj_divide.SolverStatus.COMPLETED
    assert error_queue.empty()


def test_boxed_parallel_can_be_driven_synchronously(monkeypatch):
    class FakeProcess:
        def __init__(self, target, args):
            self.target = target
            self.args = args
            self.pid = 0

        def start(self):
            self.target(*self.args)

        def is_alive(self):
            return False

        def terminate(self):
            return None

        def join(self, timeout=None):
            return None

    monkeypatch.setattr(bv_boxed_obj_divide, "Process", FakeProcess)
    monkeypatch.setattr(bv_boxed_obj_divide, "solve_objective", lambda smt2, obj_id, *_rest: _rest[-2].put(
        bv_boxed_obj_divide.ObjectiveResult(obj_id, obj_id + 4, bv_boxed_obj_divide.SolverStatus.COMPLETED, 0.01)
    ))

    x = z3.BitVec("x", 4)
    y = z3.BitVec("y", 4)
    result = bv_boxed_obj_divide.solve_boxed_parallel(z3.BoolVal(True), [x, y], engine="iter", solver_name="z3-bs")
    assert result == [4, 5]


def test_bit_blast_signed_obv_bs_path_interprets_sign_bit():
    class FakeMaxSAT:
        def solve(self):
            return [1, 1, 1]

    solver = BitBlastOMTBVSolver()
    value = solver._solve_obv_bs(FakeMaxSAT(), "x", ["b0", "b1", "b2"], is_signed=True)  # pylint: disable=protected-access
    assert value == -3


def test_pysmt_conversion_helpers_cover_symbols_and_formula():
    x = z3.BitVec("x_pysmt_conv", 4)
    y = z3.Int("y_pysmt_conv")
    b = z3.Bool("b_pysmt_conv")
    vars_out = pysmt_utils.z3_to_pysmt_vars([x, y, b])
    assert [symbol.symbol_name() for symbol in vars_out] == [
        "x_pysmt_conv",
        "y_pysmt_conv",
        "b_pysmt_conv",
    ]

    obj, formula = pysmt_utils.z3_to_pysmt(z3.And(x == 3, z3.UGE(x, 2)), x)
    assert obj.symbol_name() == "x_pysmt_conv"
    assert formula.is_and()


def test_boxed_compact_helpers_cover_mapping_and_solving():
    x = Symbol("x_compact", BVType(2))
    mapped = bv_boxed_compact.map_bitvector([[x, 1]])
    assert len(mapped) == 1
    assert len(mapped[0]) == 2

    formula = Equals(x, BV(3, 2))
    result_bits = bv_boxed_compact.solve(formula, mapped)
    assert bv_boxed_compact.res_2int(result_bits, [[x, 1]]) == [3]
