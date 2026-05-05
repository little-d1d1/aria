"""Tests for binary solver wrappers that write temporary input files."""

from pathlib import Path

import z3

from aria.pyomt import bin_solver


def test_solve_with_bin_smt_writes_expected_query_and_cleans_up(monkeypatch):
    seen = {}

    def fake_get_solver_command(solver_type, solver_name, tmp_filename):
        seen["solver_type"] = solver_type
        seen["solver_name"] = solver_name
        seen["tmp_filename"] = tmp_filename
        return ["fake-solver", tmp_filename]

    def fake_run_solver(cmd):
        tmp_path = Path(cmd[1])
        seen["file_contents"] = tmp_path.read_text(encoding="utf-8")
        return "sat\n((x 4))\n"

    monkeypatch.setattr(bin_solver, "get_solver_command", fake_get_solver_command)
    monkeypatch.setattr(bin_solver, "run_solver", fake_run_solver)

    x = z3.Int("x")
    result = bin_solver.solve_with_bin_smt("LIA", x >= 4, "x", "z3")

    assert result == "sat\n((x 4))\n"
    assert seen["solver_type"] == "smt"
    assert seen["solver_name"] == "z3"
    assert "(set-logic LIA)" in seen["file_contents"]
    assert "(get-value (x))" in seen["file_contents"]
    assert not Path(seen["tmp_filename"]).exists()


def test_solve_with_bin_maxsat_writes_wcnf_and_cleans_up(monkeypatch):
    seen = {}

    def fake_get_solver_command(solver_type, solver_name, tmp_filename):
        seen["solver_type"] = solver_type
        seen["solver_name"] = solver_name
        seen["tmp_filename"] = tmp_filename
        return ["fake-maxsat", tmp_filename]

    def fake_run_solver(cmd):
        tmp_path = Path(cmd[1])
        seen["file_contents"] = tmp_path.read_text(encoding="utf-8")
        return "sat\n"

    monkeypatch.setattr(bin_solver, "get_solver_command", fake_get_solver_command)
    monkeypatch.setattr(bin_solver, "run_solver", fake_run_solver)

    result = bin_solver.solve_with_bin_maxsat("p wcnf 1 1\n1 1 0\n", "z3")

    assert result == "sat\n"
    assert seen["solver_type"] == "maxsat"
    assert seen["solver_name"] == "z3"
    assert seen["file_contents"] == "p wcnf 1 1\n1 1 0\n"
    assert not Path(seen["tmp_filename"]).exists()
