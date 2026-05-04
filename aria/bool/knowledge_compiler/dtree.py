"""
Decision-tree helpers for knowledge compilation.
"""

from __future__ import annotations

from typing import Dict, List, Optional


class Node:
    """Represents a node in a decision tree (dtree)."""

    def __init__(
        self,
        node_id: Optional[int] = None,
        left_child: Optional["Node"] = None,
        right_child: Optional["Node"] = None,
        clause: Optional[List[int]] = None,
    ) -> None:
        self.node_id: Optional[int] = node_id
        self.left_child: Optional["Node"] = left_child
        self.right_child: Optional["Node"] = right_child
        self.clauses: List[List[int]] = []
        self.atoms: List[int] = []
        self.separators: List[int] = []
        self.clause_key: List[int] = []
        self.lit_key = 0

        if clause is not None and (left_child is not None or right_child is not None):
            raise ValueError("A dtree node cannot be both a leaf and an internal node")
        if (left_child is None) != (right_child is None):
            raise ValueError("A dtree internal node must have both children present")

        if clause is not None:
            self.clauses = [list(clause)]
            self.atoms = sorted({abs(lit) for lit in clause})
            self.separators = []
            self.clause_key = [1 if len(clause) == 0 else 0]
        elif left_child is not None and right_child is not None:
            self.refresh_metadata()

        self.validate()

    def refresh_metadata(self) -> None:
        """Recompute the derived metadata of this node from its children."""
        if self.is_leaf():
            return
        assert self.left_child is not None
        assert self.right_child is not None
        self.clauses = list(self.left_child.clauses) + list(self.right_child.clauses)
        left_atoms = set(self.left_child.atoms)
        right_atoms = set(self.right_child.atoms)
        self.atoms = sorted(left_atoms | right_atoms)
        self.separators = sorted(left_atoms & right_atoms)
        self.clause_key = list(self.left_child.clause_key) + list(
            self.right_child.clause_key
        )
        self.validate()

    def validate(self) -> None:
        """Validate basic structural invariants."""
        if self.is_leaf():
            if self.left_child is not None or self.right_child is not None:
                raise ValueError("Leaf nodes cannot have children")
            if len(self.clauses) != 1 or len(self.clause_key) != 1:
                raise ValueError("Leaf nodes must own exactly one clause and one key bit")
            expected_atoms = sorted({abs(lit) for lit in self.clauses[0]})
            if self.atoms != expected_atoms:
                raise ValueError("Leaf atom metadata is inconsistent with the clause")
            if self.separators:
                raise ValueError("Leaf nodes cannot have separators")
        else:
            if self.left_child is None or self.right_child is None:
                raise ValueError("Internal nodes must have both children")
            expected_clauses = self.left_child.clauses + self.right_child.clauses
            if self.clauses != expected_clauses:
                raise ValueError("Internal node clauses must be the concatenation of children")
            expected_atoms = sorted(
                set(self.left_child.atoms).union(self.right_child.atoms)
            )
            if self.atoms != expected_atoms:
                raise ValueError("Internal node atoms are inconsistent with children")
            expected_separators = sorted(
                set(self.left_child.atoms).intersection(self.right_child.atoms)
            )
            if self.separators != expected_separators:
                raise ValueError("Internal node separators are inconsistent with children")
            expected_clause_key = self.left_child.clause_key + self.right_child.clause_key
            if self.clause_key != expected_clause_key:
                raise ValueError("Internal node clause keys are inconsistent with children")

    def is_leaf(self) -> bool:
        """Check if this is a leaf node."""
        return self.left_child is None and self.right_child is None

    def is_full_binary(self) -> bool:
        """Check if this is a full binary tree."""
        if self.is_leaf():
            return True
        assert self.left_child is not None
        assert self.right_child is not None
        return self.left_child.is_full_binary() and self.right_child.is_full_binary()

    def get_counter(self) -> Dict[int, int]:
        """
        Count occurrences of literals in clauses.
        """
        counter: Dict[int, int] = {}
        for clause in self.clauses:
            for literal in clause:
                counter[literal] = counter.get(literal, 0) + 1
        return counter

    def pick_most(self) -> int:
        """
        Pick a separator variable with the most occurrences.
        """
        if not self.separators:
            raise ValueError("Cannot pick a separator variable when no separator exists")
        counter = self.get_counter()
        best_var = self.separators[0]
        best_count = -1
        for var in self.separators:
            count = counter.get(var, 0) + counter.get(-var, 0)
            if count > best_count:
                best_var = var
                best_count = count
        return best_var

    def print_info(
        self, leaf: List[int], output_file: Optional[str] = None
    ) -> List[int]:
        """
        Print node information in the legacy dtree format.
        """
        if self.is_leaf():
            if output_file is not None:
                with open(output_file, "a", encoding="utf-8") as out:
                    out.write(f"L {self.node_id}\n")
            else:
                print("L ", self.node_id)
            leaf.append(int(self.node_id))
            return leaf

        assert self.left_child is not None
        assert self.right_child is not None
        leaf = self.left_child.print_info(leaf, output_file)
        leaf = self.right_child.print_info(leaf, output_file)
        left_child_pos = self.left_child.node_id
        right_child_pos = self.right_child.node_id
        if self.left_child.node_id in leaf:
            left_child_pos = leaf.index(int(self.left_child.node_id))
        if self.right_child.node_id in leaf:
            right_child_pos = leaf.index(int(self.right_child.node_id))
        if output_file is not None:
            with open(output_file, "a", encoding="utf-8") as out:
                out.write(f"I {left_child_pos} {right_child_pos}\n")
        else:
            print("I ", left_child_pos, right_child_pos)
        return leaf


class Dtree_Compiler:
    """Compiler for constructing decision trees from CNF formulas."""

    def __init__(self, clausal_form: List[List[int]]) -> None:
        self.node_id = 0
        self.clausal_form = [list(clause) for clause in clausal_form]

    def default_ordering(self, strategy: str = "appearance") -> List[int]:
        """
        Compute a deterministic variable ordering for the current CNF.

        Strategies:
        - ``appearance``: first-appearance order in the input clauses
        - ``frequency``: descending variable frequency, then variable id
        """
        variables = [abs(lit) for clause in self.clausal_form for lit in clause]
        if strategy == "appearance":
            ordering: List[int] = []
            seen = set()
            for var in variables:
                if var not in seen:
                    seen.add(var)
                    ordering.append(var)
            return ordering
        if strategy == "frequency":
            counts: Dict[int, int] = {}
            first_index: Dict[int, int] = {}
            for index, var in enumerate(variables):
                counts[var] = counts.get(var, 0) + 1
                first_index.setdefault(var, index)
            return sorted(
                counts,
                key=lambda var: (-counts[var], first_index[var], var),
            )
        raise ValueError(f"Unknown dtree ordering strategy: {strategy}")

    def compose(self, list_tree: List[Node]) -> Node:
        """
        Compose nodes into a right-associated binary tree in stable order.
        """
        if not list_tree:
            raise ValueError("Cannot compose an empty dtree node list")
        if len(list_tree) == 1:
            return list_tree[0]

        current = list_tree[-1]
        for node in reversed(list_tree[:-1]):
            current = Node(
                node_id=self.node_id,
                left_child=node,
                right_child=current,
            )
            self.node_id += 1
        return current

    def el2dt(
        self, ordering: Optional[List[int]] = None, strategy: str = "appearance"
    ) -> Node:
        """
        Construct a dtree according to a given variable ordering.
        """
        sigma: List[Node] = []
        for clause in self.clausal_form:
            leaf = Node(node_id=self.node_id, clause=clause)
            self.node_id += 1
            sigma.append(leaf)

        if ordering is None:
            ordering = self.default_ordering(strategy=strategy)

        seen = set()
        stable_ordering: List[int] = []
        for lit in ordering:
            var = abs(lit)
            if var not in seen:
                seen.add(var)
                stable_ordering.append(var)

        for var in stable_ordering:
            t_nodes = [node for node in sigma if var in node.atoms]
            if not t_nodes:
                continue
            composed_node = self.compose(t_nodes)
            sigma = [node for node in sigma if var not in node.atoms]
            sigma.append(composed_node)

        return self.compose(sigma)
