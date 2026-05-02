"""Regression tests for the EFMC Farkas encoding."""

import re
from typing import Sequence

import z3

from aria.efmc.engines.ef.farkas.farkas_lemma import FarkasLemma


def _is_sat(constraints: Sequence[z3.BoolRef]) -> bool:
    solver = z3.Solver()
    solver.add(constraints)
    return solver.check() == z3.sat


def test_symbolic_entailment_uses_polyhorn_farkas_shape():
    x = z3.Real("x")
    lemma = FarkasLemma()
    lemma.add_constraint(x >= 0)
    lemma.add_constraint(x <= 1)

    constraints = lemma.apply_entailment_symbolic(x >= 0, [x])

    assert _is_sat(constraints)


def test_symbolic_entailment_rejects_unprovable_conclusion():
    x = z3.Real("x")
    lemma = FarkasLemma()
    lemma.add_constraint(x >= 0)

    constraints = lemma.apply_entailment_symbolic(x >= 1, [x])

    assert not _is_sat(constraints)


def test_symbolic_entailment_splits_equalities():
    x = z3.Real("x")
    lemma = FarkasLemma()
    lemma.add_constraint(x == 0)

    constraints = lemma.apply_entailment_symbolic(x >= 0, [x])

    assert _is_sat(constraints)


def test_symbolic_entailment_uses_fresh_lambda_names():
    x = z3.Real("x")
    first = FarkasLemma()
    second = FarkasLemma()
    first.add_constraint(x >= 0)
    second.add_constraint(x >= 0)

    first_constraints = first.apply_entailment_symbolic(x >= 0, [x])
    second_constraints = second.apply_entailment_symbolic(x >= 0, [x])

    first_text = "\n".join(str(constraint) for constraint in first_constraints)
    second_text = "\n".join(str(constraint) for constraint in second_constraints)
    first_names = set(re.findall(r"farkas_lambda_\d+_\d+", first_text))
    second_names = set(re.findall(r"farkas_lambda_\d+_\d+", second_text))
    assert first_names
    assert second_names
    assert first_names.isdisjoint(second_names)
