"""Regression tests for the Z3-facing Putinar lemma adapter."""

from typing import Sequence

import z3

from aria.efmc.engines.ef.farkas.putinar_lemma import PutinarLemma
from aria.efmc.engines.ef.farkas.farkas_template import FarkasTemplate
from aria.efmc.sts import TransitionSystem


def _is_sat(constraints: Sequence[z3.BoolRef]) -> bool:
    solver = z3.Solver()
    solver.add(constraints)
    return solver.check() == z3.sat


def test_putinar_entailment_proves_square_nonnegative():
    x = z3.Real("x")
    lemma = PutinarLemma(max_degree=2)

    constraints = lemma.apply_entailment_symbolic(x * x >= 0, [x])

    assert _is_sat(constraints)


def test_putinar_entailment_uses_premise_multiplier():
    x = z3.Real("x")
    lemma = PutinarLemma(max_degree=2)
    lemma.add_constraint(x >= 0)

    constraints = lemma.apply_entailment_symbolic(x * x >= 0, [x])

    assert _is_sat(constraints)


def test_putinar_entailment_splits_equality_premises():
    x = z3.Real("x")
    lemma = PutinarLemma(max_degree=2)
    lemma.add_constraint(x == 0)

    constraints = lemma.apply_entailment_symbolic(x >= 0, [x])

    assert _is_sat(constraints)


def test_putinar_entailment_rejects_invalid_positive_constant_bound():
    x = z3.Real("x")
    lemma = PutinarLemma(max_degree=2)

    constraints = lemma.apply_entailment_symbolic(x * x - 1 >= 0, [x])

    assert not _is_sat(constraints)


def test_farkas_template_can_select_putinar_backend():
    x, x_prime = z3.Reals("x x_prime")
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=x == 0,
        trans=x_prime == x,
        post=x >= 0,
    )

    template = FarkasTemplate(
        sts,
        num_templates=1,
        positivity_lemma="putinar",
        putinar_max_degree=2,
    )

    assert template.template_cnt_init_and_post is not None
    assert template.template_cnt_trans is not None
