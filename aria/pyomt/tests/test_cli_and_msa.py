"""Tests for CLI argument plumbing and MSA modules."""

import sys
import tempfile
from pathlib import Path

import z3
from pysmt.shortcuts import Or, Symbol
from pysmt.typing import BOOL

from aria.pyomt import omt_solver
from aria.pyomt.msa.mistral_msa import MSASolver
from aria.pyomt.msa.mistral_pysmt import Mistral, get_qmodel


def test_cli_main_passes_bv_specific_options(monkeypatch):
    captured = {}

    def fake_solve_opt_file(*args, **kwargs):
        captured["args"] = args
        captured["kwargs"] = kwargs
        return "ok"

    monkeypatch.setattr(omt_solver, "solve_opt_file", fake_solve_opt_file)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "omt_solver.py",
            "example.smt2",
            "--engine",
            "qsmt",
            "--opt-theory-bv-engine",
            "iter",
            "--solver-iter",
            "z3-bs",
            "--opt-box-engine",
            "compact",
            "--opt-box-shuffle",
        ],
    )

    omt_solver.main()

    assert captured["args"][:4] == ("example.smt2", "qsmt", "z3-bs", "box")
    assert captured["kwargs"]["bv_engine"] == "iter"
    assert captured["kwargs"]["opt_box_engine"] == "compact"
    assert captured["kwargs"]["opt_box_shuffle"] is True


def test_cli_main_passes_integer_theory_override(monkeypatch):
    captured = {}

    monkeypatch.setattr(omt_solver, "solve_opt_file", lambda *args, **kwargs: captured.update(args=args, kwargs=kwargs))
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "omt_solver.py",
            "arith.smt2",
            "--engine",
            "maxsat",
            "--opt-theory-int-engine",
            "iter",
        ],
    )

    omt_solver.main()

    assert captured["args"][:4] == ("arith.smt2", "maxsat", "z3", "box")
    assert captured["kwargs"]["int_engine"] == "iter"


def test_msa_solver_finds_small_model():
    a, b, c, d = z3.Ints("a b c d")
    fml = z3.Or(z3.And(a == 3, b == 3), z3.And(a == 1, b == 1, c == 1, d == 1))

    solver = MSASolver(verbose=0)
    solver.init_from_formula(fml)
    model = solver.find_small_model()

    assert model is not None
    assert solver.validate_small_model(model)


def test_get_qmodel_finds_existential_assignment():
    x = Symbol("x_bool_qmodel", BOOL)
    y = Symbol("y_bool_qmodel", BOOL)

    candidate = get_qmodel({x}, Or(x, y), solver_name="z3")

    assert candidate is not None
    assert str(candidate[y]) == "True"


def test_mistral_solver_can_parse_and_solve_file(tmp_path):
    smt2 = tmp_path / "msa.smt2"
    smt2.write_text(
        "\n".join(
            [
                "(set-logic QF_BOOL)",
                "(declare-fun a () Bool)",
                "(declare-fun b () Bool)",
                "(assert (or a b))",
                "(check-sat)",
            ]
        ),
        encoding="utf-8",
    )

    solver = Mistral(simplify=True, solver="z3", qsolve="std", verbose=0, fname=str(smt2))
    result = solver.solve()

    assert result is not None
    assert len(result) == 1
