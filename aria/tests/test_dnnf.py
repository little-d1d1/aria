# coding: utf-8
"""
Semantic tests for the knowledge compilation DNNF engine.
"""

from __future__ import annotations

import copy
import itertools

from pysat.formula import CNF

from aria.tests import TestCase, main
from aria.bool.knowledge_compiler import compile_dnnf
from aria.bool.knowledge_compiler.dimacs_parser import parse_cnf_string
from aria.bool.knowledge_compiler.dnnf import DNF_Node, DNNF_Compiler
from aria.bool.knowledge_compiler.dtree import Dtree_Compiler
from examples.prob import WMCOptions, compile_wmc, wmc_count

cnf_foo2 = """
p cnf 4 4
1 2 3 0
-2 3 4 0
1 -4 0
2 3 -4 0
"""


def _all_assignments(variables):
    for values in itertools.product([False, True], repeat=len(variables)):
        yield dict(zip(variables, values))


def _eval_cnf(clauses, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def _eval_dnnf(node: DNF_Node, assignment):
    if node.type == "L":
        if isinstance(node.literal, bool):
            return bool(node.literal)
        return assignment[abs(node.literal)] == (node.literal > 0)
    if node.type == "A":
        return _eval_dnnf(node.left_child, assignment) and _eval_dnnf(node.right_child, assignment)
    return _eval_dnnf(node.left_child, assignment) or _eval_dnnf(node.right_child, assignment)


def _project_assignment(assignment, keep):
    return tuple(sorted((var, value) for var, value in assignment.items() if var in keep))


class TestDNNF(TestCase):

    def _compile(self, clauses, ordering=None):
        if ordering is None:
            ordering = sorted({abs(lit) for clause in clauses for lit in clause})
        dtree = Dtree_Compiler([list(clause) for clause in clauses]).el2dt(ordering)
        compiler = DNNF_Compiler(dtree)
        dnnf = compiler.compile()
        self.assertIsNotNone(dnnf)
        return compiler, dnnf

    def test_dnnf_semantics_match_cnf(self):
        clausal_form, _ = parse_cnf_string(cnf_foo2, True)
        compiler, dnnf = self._compile(clausal_form, [2, 3, 4, 1])
        variables = [1, 2, 3, 4]

        compiler.validate(dnnf)
        self.assertTrue(compiler.is_decomposable(dnnf))
        self.assertTrue(compiler.is_deterministic(dnnf))

        for assignment in _all_assignments(variables):
            self.assertEqual(
                _eval_cnf(clausal_form, assignment),
                _eval_dnnf(dnnf, assignment),
            )

        self.assertTrue(compiler.is_sat(dnnf))
        self.assertEqual(compiler.model_count(dnnf), len(compiler.enumerate_models(dnnf)))
        self.assertIsNotNone(compiler.one_model(dnnf))

    def test_single_clause_root_compiles(self):
        compiler, dnnf = self._compile([[1, 2]], [1, 2])
        self.assertEqual(dnnf.type, "O")
        self.assertTrue(compiler.is_sat(dnnf))
        self.assertEqual(sorted(compiler.enumerate_models(dnnf)), [[-1, 2], [1]])

    def test_unit_clause_root_compiles(self):
        compiler, dnnf = self._compile([[1]], [1])
        self.assertEqual(dnnf.type, "L")
        self.assertEqual(dnnf.literal, 1)
        self.assertTrue(compiler.is_sat(dnnf))

    def test_unsat_cnf_compiles_to_false(self):
        compiler, dnnf = self._compile([[1], [-1]], [1])
        self.assertEqual(dnnf.type, "L")
        self.assertFalse(dnnf.literal)
        self.assertFalse(compiler.is_sat(dnnf))
        self.assertEqual(compiler.enumerate_models(dnnf), [])

    def test_unit_propagation_to_true_leaf(self):
        compiler, dnnf = self._compile([[1], [2]], [1, 2])
        self.assertTrue(compiler.is_sat(dnnf))
        self.assertEqual(compiler.enumerate_models(dnnf), [[1, 2]])

    def test_conditioning_and_conjoin_preserve_semantics(self):
        clauses = [[1, 2], [-1, 3]]
        compiler, dnnf = self._compile(clauses, [1, 2, 3])
        conditioned = compiler.simplify(compiler.conditioning(copy.deepcopy(dnnf), [1]))
        conjoined = compiler.simplify(compiler.conjoin(copy.deepcopy(dnnf), [1]))

        for assignment in _all_assignments([1, 2, 3]):
            expected_conditioned = _eval_cnf(clauses, {**assignment, 1: True})
            expected_conjoined = _eval_cnf(clauses + [[1]], assignment)
            self.assertEqual(_eval_dnnf(conditioned, assignment), expected_conditioned)
            self.assertEqual(_eval_dnnf(conjoined, assignment), expected_conjoined)

    def test_projection_matches_existential_forgetting(self):
        clauses = [[1, 2], [-1, 3]]
        compiler, dnnf = self._compile(clauses, [1, 2, 3])
        projected = compiler.simplify(compiler.project(copy.deepcopy(dnnf), [2, 3]))
        keep = {2, 3}

        projected_truth = {}
        for assignment in _all_assignments([2, 3]):
            projected_truth[_project_assignment(assignment, keep)] = _eval_dnnf(projected, assignment)

        for assignment in _all_assignments([2, 3]):
            expected = False
            for forgotten_value in [False, True]:
                full = dict(assignment)
                full[1] = forgotten_value
                expected = expected or _eval_cnf(clauses, full)
            self.assertEqual(projected_truth[_project_assignment(assignment, keep)], expected)

    def test_smoothing_preserves_semantics_and_aligns_atoms(self):
        clauses = [[1, 2], [-1, 3]]
        compiler, dnnf = self._compile(clauses, [1, 2, 3])
        smooth = compiler.smooth(copy.deepcopy(dnnf))

        def assert_smoothed(node):
            if node.type == "L":
                return
            if node.type == "O":
                self.assertEqual(sorted(node.left_child.atoms), sorted(node.right_child.atoms))
            assert_smoothed(node.left_child)
            assert_smoothed(node.right_child)

        assert_smoothed(smooth)
        for assignment in _all_assignments([1, 2, 3]):
            self.assertEqual(_eval_dnnf(dnnf, assignment), _eval_dnnf(smooth, assignment))
        self.assertTrue(compiler.is_smooth(smooth))

    def test_minimize_keeps_minimum_negative_model_count(self):
        compiler, dnnf = self._compile([[-1], [2]], [1, 2])
        minimized = compiler.minimize(copy.deepcopy(dnnf))
        self.assertEqual(compiler.m_card(minimized), compiler.m_card(dnnf))
        self.assertEqual(compiler.enumerate_models(minimized), [[-1, 2]])

    def test_compile_wmc_uses_exact_backend_on_leaf_cases(self):
        cnf = CNF(from_clauses=[[1]])
        weights = {1: 0.4, -1: 0.6}

        compiled = compile_wmc(cnf, weights, WMCOptions(strict_complements=True))
        self.assertEqual(compiled.backend, "wmc-dnnf")
        self.assertEqual(wmc_count(cnf, weights), 0.4)

    def test_public_compiled_dnnf_wrapper_and_nnf_bridge(self):
        compiled = compile_dnnf([[1, 2], [-1, 3]], ordering_strategy="frequency")
        compiled.validate()
        self.assertTrue(compiled.is_sat())
        self.assertTrue(compiled.is_decomposable())
        self.assertTrue(compiled.is_deterministic())
        self.assertEqual(compiled.model_count(), len(compiled.enumerate_models()))
        self.assertIsNotNone(compiled.one_model())

        conditioned = compiled.condition([1])
        projected = compiled.project([2, 3])
        smoothed = compiled.smooth()
        minimized = compiled.minimize()
        self.assertTrue(conditioned.is_sat())
        self.assertTrue(smoothed.is_smooth())
        self.assertLessEqual(minimized.model_count(), compiled.model_count())

        nnf_sentence = compiled.to_nnf()
        self.assertTrue(nnf_sentence.decomposable())
        self.assertTrue(nnf_sentence.marked_deterministic())
        for assignment in _all_assignments([1, 2, 3]):
            self.assertEqual(
                nnf_sentence.satisfied_by(assignment),
                _eval_dnnf(compiled.root, assignment),
            )
        for assignment in _all_assignments([2, 3]):
            self.assertEqual(
                projected.to_nnf().satisfied_by(assignment),
                _eval_dnnf(projected.root, assignment),
            )


if __name__ == "__main__":
    main()
