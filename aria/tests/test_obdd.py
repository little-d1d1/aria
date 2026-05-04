# coding: utf-8
"""
Semantic tests for the knowledge compilation OBDD engine.
"""

from __future__ import annotations

import itertools

from aria.tests import TestCase, main
from aria.bool.knowledge_compiler import compile_obdd
from aria.bool.knowledge_compiler.dimacs_parser import parse_cnf_string
from aria.bool.knowledge_compiler.obdd import BDD, BDD_Compiler

cnf_foo3 = """
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


def _eval_bdd(node: BDD, assignment):
    if node.is_sink():
        return bool(node.var)
    branch = node.high if assignment[node.var] else node.low
    return _eval_bdd(branch, assignment)


class TestOBDD(TestCase):

    def test_obdd_semantics_and_queries(self):
        clausal_form, nvars = parse_cnf_string(cnf_foo3, True)

        for key_type in ("separator", "cutset"):
            compiler = BDD_Compiler(nvars, clausal_form)
            obdd = compiler.compile(key_type=key_type)
            compiler.validate(obdd)
            obdd.print_info(nvars)
            self.assertTrue(compiler.is_sat(obdd))
            self.assertIsNotNone(compiler.one_model(obdd))

            sat_assignments = 0
            for assignment in _all_assignments([1, 2, 3, 4]):
                expected = _eval_cnf(clausal_form, assignment)
                actual = _eval_bdd(obdd, assignment)
                self.assertEqual(expected, actual)
                if expected:
                    sat_assignments += 1

            self.assertEqual(compiler.model_count(obdd), sat_assignments)

    def test_unsat_and_tautology_terminals(self):
        unsat = BDD_Compiler(1, [[1], [-1]]).compile()
        taut = BDD_Compiler(1, []).compile()
        self.assertFalse(bool(unsat.var) if unsat.is_sink() else True)
        self.assertTrue(bool(taut.var) if taut.is_sink() else False)

    def test_public_compiled_obdd_wrapper_and_nnf_bridge(self):
        compiled = compile_obdd([[1, 2], [-1, 3]], ordering=[2, 1, 3], key_type="separator")
        compiled.validate()
        self.assertTrue(compiled.is_sat())
        self.assertEqual(compiled.model_count(), 4)
        self.assertIsNotNone(compiled.one_model())
        self.assertEqual(compiled.one_model(), compiled.enumerate_models()[0])
        self.assertEqual(len(compiled.enumerate_models()), compiled.model_count())

        conditioned = compiled.condition([1])
        self.assertEqual(conditioned.variables, [2, 3])
        self.assertEqual(conditioned.model_count(), 2)
        self.assertEqual(conditioned.enumerate_models(), [[-2, 3], [2, 3]])

        projected = compiled.project([2, 3])
        forgotten = compiled.forget([1])
        for assignment in _all_assignments([2, 3]):
            projected_value = projected.satisfied_by(assignment)
            forgotten_value = forgotten.satisfied_by(assignment)
            expected = False
            for value_1 in (False, True):
                full = dict(assignment)
                full[1] = value_1
                expected = expected or _eval_bdd(compiled.root, full)
            self.assertEqual(projected_value, expected)
            self.assertEqual(forgotten_value, expected)

        nnf_sentence = compiled.to_nnf()
        self.assertTrue(nnf_sentence.decomposable())
        self.assertTrue(nnf_sentence.marked_deterministic())
        for assignment in _all_assignments([1, 2, 3]):
            self.assertEqual(
                nnf_sentence.satisfied_by(assignment),
                _eval_bdd(compiled.root, assignment),
            )


if __name__ == "__main__":
    main()
