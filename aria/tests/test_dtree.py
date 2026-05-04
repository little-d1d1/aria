# coding: utf-8
"""
Tests for dtree construction and DIMACS parsing.
"""

from aria.tests import TestCase, main
from aria.bool.knowledge_compiler.dimacs_parser import parse_cnf_string
from aria.bool.knowledge_compiler.dtree import Dtree_Compiler

cnf_foo = """
c example
p cnf 4 4
1 2 3 0
-2 3 4 0
1 -4 0
2 3 -4 0
"""


class TestDTree(TestCase):

    def test_dtree(self):
        clausal_form, _ = parse_cnf_string(cnf_foo, True)
        dtree_compiler = Dtree_Compiler(clausal_form)
        dtree = dtree_compiler.el2dt([2, 3, 4, 1])
        leaf = dtree.print_info([])
        self.assertEqual(dtree.separators, [1, 4])
        self.assertEqual(dtree.atoms, [1, 2, 3, 4])
        self.assertTrue(dtree.left_child.is_leaf())
        self.assertTrue(dtree.is_full_binary())
        self.assertEqual(sorted(dtree.clauses), sorted(clausal_form))
        self.assertEqual(len(leaf), len(clausal_form))

    def test_dimacs_parser_handles_comments_and_blank_lines(self):
        cnf = """
c header comment

p cnf 2 2
1   -2 0
c inline comment
2 0
"""
        clauses, nvars = parse_cnf_string(cnf)
        self.assertEqual(clauses, [[1, -2], [2]])
        self.assertEqual(nvars, 2)

    def test_dimacs_parser_rejects_unterminated_clause(self):
        with self.assertRaises(ValueError):
            parse_cnf_string("p cnf 1 1\n1")

    def test_dtree_is_deterministic_for_same_input(self):
        clauses, _ = parse_cnf_string(cnf_foo)
        compiler_a = Dtree_Compiler(clauses)
        compiler_b = Dtree_Compiler(clauses)
        tree_a = compiler_a.el2dt([2, 3, 4, 1])
        tree_b = compiler_b.el2dt([2, 3, 4, 1])
        self.assertEqual(tree_a.clauses, tree_b.clauses)
        self.assertEqual(tree_a.atoms, tree_b.atoms)
        self.assertEqual(tree_a.separators, tree_b.separators)

    def test_default_ordering_strategies(self):
        clauses, _ = parse_cnf_string(cnf_foo)
        compiler = Dtree_Compiler(clauses)
        self.assertEqual(compiler.default_ordering("appearance"), [1, 2, 3, 4])
        self.assertEqual(compiler.default_ordering("frequency"), [2, 3, 4, 1])
        tree = compiler.el2dt(ordering=None, strategy="frequency")
        self.assertTrue(tree.is_full_binary())


if __name__ == "__main__":
    main()
