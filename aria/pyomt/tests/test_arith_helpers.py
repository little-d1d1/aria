"""Tests for arithmetic optimization helpers."""

import pytest
import z3

pytest.importorskip("pulp")

from aria.pyomt.omtarith import arith_opt_lp, arith_opt_ls, arith_opt_qsmt


def test_arith_opt_with_qsmt_builds_lia_query(monkeypatch):
    captured = {}

    def fake_solve_with_bin_smt(logic, qfml, obj_name, solver_name):
        captured["logic"] = logic
        captured["qfml"] = qfml
        captured["obj_name"] = obj_name
        captured["solver_name"] = solver_name
        return "sat\n((x 4))"

    monkeypatch.setattr(arith_opt_qsmt, "solve_with_bin_smt", fake_solve_with_bin_smt)

    x = z3.Int("x")
    result = arith_opt_qsmt.arith_opt_with_qsmt(x >= 4, x, minimize=True, solver_name="z3")

    assert result == "sat\n((x 4))"
    assert captured["logic"] == "LIA"
    assert captured["obj_name"] == "x"
    assert captured["solver_name"] == "z3"
    assert "ForAll" in str(captured["qfml"])
    assert "x <= xm" in str(captured["qfml"])


def test_arith_opt_with_qsmt_builds_lra_query(monkeypatch):
    captured = {}

    def fake_solve_with_bin_smt(logic, qfml, obj_name, solver_name):
        captured["logic"] = logic
        captured["qfml"] = qfml
        return "sat\n((r (/ 3 2)))"

    monkeypatch.setattr(arith_opt_qsmt, "solve_with_bin_smt", fake_solve_with_bin_smt)

    r = z3.Real("r")
    arith_opt_qsmt.arith_opt_with_qsmt(r <= z3.RealVal("3/2"), r, minimize=False, solver_name="z3")

    assert captured["logic"] == "LRA"
    assert "rm <= r" in str(captured["qfml"])


def test_arith_opt_with_ls_finds_integer_minimum():
    x = z3.Int("x")
    result = arith_opt_ls.arith_opt_with_ls(z3.And(x >= 4, x <= 9), x, minimize=True, solver_name="z3")
    assert result == "4"


def test_arith_opt_with_ls_reports_unsat():
    x = z3.Int("x")
    result = arith_opt_ls.arith_opt_with_ls(z3.And(x >= 4, x <= 3), x, minimize=True, solver_name="z3")
    assert result == "unsat"


def test_lp_convexity_helpers_distinguish_conjunctions_and_disjunctions():
    x, y = z3.Ints("x y")
    assert arith_opt_lp._is_convex_problem(z3.And(x >= 0, y <= 2))
    assert not arith_opt_lp._is_convex_problem(z3.Or(x >= 0, y <= 2))


def test_lp_conversion_helpers_build_constraints_and_objective():
    x, y = z3.Ints("x_lp_conv y_lp_conv")
    vars_map = arith_opt_lp._extract_variables(z3.And(x + y <= 5, x >= 1), x + 2 * y)

    constraints = arith_opt_lp._convert_to_lp_constraints(
        z3.And(x + y <= 5, x >= 1),
        vars_map,
    )
    objective = arith_opt_lp._convert_to_lp_objective(x + 2 * y, vars_map)

    assert len(constraints) == 2
    assert "x_lp_conv" in str(constraints[0]) or "x_lp_conv" in str(constraints[1])
    assert "y_lp_conv" in str(objective)


def test_arith_opt_with_lp_solves_simple_integer_problem():
    x = z3.Int("x_lp_solve")
    value, model = arith_opt_lp.arith_opt_with_lp(
        z3.And(x >= 4, x <= 9),
        x,
        minimize=True,
        solver_name="pulp",
    )

    assert value == 4.0
    assert model is not None
    assert model["x_lp_solve"] == 4.0
