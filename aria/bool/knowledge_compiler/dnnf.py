"""
DNNF (Decomposable Negation Normal Form) compilation helpers.
"""

from __future__ import annotations

import copy
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple, Union

from aria.bool.knowledge_compiler.dtree import Node
from aria.bool import nnf as aria_nnf

Clause = Tuple[int, ...]
FormulaState = Tuple[Clause, ...]


class DNF_Node:
    """Represents a node in a DNNF tree."""

    def __init__(
        self,
        node_type: str,
        left_child: Optional["DNF_Node"] = None,
        right_child: Optional["DNF_Node"] = None,
        literal: Optional[Union[int, bool]] = None,
        conflict_atom: Optional[int] = None,
    ) -> None:
        if node_type not in ("A", "O", "L"):
            raise ValueError(f"Unknown DNNF node type: {node_type}")
        self.type = node_type
        self.left_child = left_child
        self.right_child = right_child
        self.conflict_atom = conflict_atom
        self.explore_id: Optional[int] = None
        self.models: Optional[List[Dict[int, bool]]] = None
        self._literal_value: Optional[int] = None
        self.constant_value: Optional[bool] = None

        if self.type == "L":
            if literal is None:
                raise ValueError("Leaf DNNF nodes must carry a literal or boolean")
            if isinstance(literal, bool):
                self.constant_value = literal
                self.atoms = []
            else:
                self._literal_value = int(literal)
                self.atoms = [abs(int(literal))]
        else:
            if left_child is None or right_child is None:
                raise ValueError("Internal DNNF nodes must have two children")
            self.atoms = sorted(set(left_child.atoms).union(right_child.atoms))

    @property
    def literal(self) -> Optional[Union[int, bool]]:
        """Legacy literal view kept for compatibility."""
        if self.constant_value is not None:
            return self.constant_value
        return self._literal_value

    @literal.setter
    def literal(self, value: Optional[Union[int, bool]]) -> None:
        if value is None:
            self._literal_value = None
            self.constant_value = None
        elif isinstance(value, bool):
            self._literal_value = None
            self.constant_value = value
            self.atoms = []
        else:
            self._literal_value = int(value)
            self.constant_value = None
            self.atoms = [abs(int(value))]

    def is_literal_leaf(self) -> bool:
        return self.type == "L" and self.constant_value is None

    def is_boolean_leaf(self) -> bool:
        return self.type == "L" and self.constant_value is not None

    def validate(self) -> None:
        """Validate structural invariants for this node."""
        if self.type == "L":
            if self.left_child is not None or self.right_child is not None:
                raise ValueError("DNNF literal nodes cannot have children")
            if self.constant_value is None and self._literal_value is None:
                raise ValueError("DNNF leaf nodes must carry a constant or literal")
            expected_atoms = (
                []
                if self.constant_value is not None
                else [abs(int(self._literal_value))]
            )
            if self.atoms != expected_atoms:
                raise ValueError("DNNF leaf atom metadata is inconsistent")
            return

        if self.left_child is None or self.right_child is None:
            raise ValueError("Internal DNNF nodes must have two children")
        expected_atoms = sorted(set(self.left_child.atoms).union(self.right_child.atoms))
        if self.atoms != expected_atoms:
            raise ValueError("Internal DNNF node atoms are inconsistent with children")

    def count_node(self, current_id: int) -> int:
        """Count nodes in the DNNF DAG."""
        if self.explore_id is not None:
            return current_id
        if self.type != "L":
            assert self.left_child is not None and self.right_child is not None
            current_id = self.left_child.count_node(current_id)
            current_id = self.right_child.count_node(current_id)
        self.explore_id = current_id
        return current_id + 1

    def count_edge(self) -> int:
        """Count edges in the DNNF DAG."""
        if self.type == "L":
            return 0
        assert self.left_child is not None and self.right_child is not None
        return self.left_child.count_edge() + self.right_child.count_edge() + 2

    def collect_var(self) -> List[int]:
        """Collect variables appearing in the DNNF."""
        if self.type == "L":
            if isinstance(self.literal, bool):
                return []
            return [abs(int(self.literal))]
        assert self.left_child is not None and self.right_child is not None
        return sorted(set(self.left_child.collect_var()).union(self.right_child.collect_var()))

    def print_nnf(self, current_id: int, output_file: Optional[str] = None) -> int:
        """Print DNNF in the legacy NNF interchange format."""
        if self.explore_id is not None:
            return current_id

        if self.type == "L":
            encoded_literal = (
                1 if self.literal is True else 0 if self.literal is False else self.literal
            )
            if output_file is not None:
                with open(output_file, "a", encoding="utf-8") as out:
                    out.write(f"L {encoded_literal}\n")
            else:
                print(f"{current_id} L {encoded_literal}")
        else:
            assert self.left_child is not None and self.right_child is not None
            current_id = self.left_child.print_nnf(current_id, output_file)
            current_id = self.right_child.print_nnf(current_id, output_file)
            if self.type == "A":
                line = f"A 2 {self.left_child.explore_id} {self.right_child.explore_id}\n"
            else:
                line = (
                    f"O {self.conflict_atom or 0} 2 "
                    f"{self.left_child.explore_id} {self.right_child.explore_id}\n"
                )
            if output_file is not None:
                with open(output_file, "a", encoding="utf-8") as out:
                    out.write(line)
            else:
                print(f"{current_id} {line.strip()}")
        self.explore_id = current_id
        return current_id + 1

    def reset(self) -> None:
        """Reset traversal state."""
        self.explore_id = None
        if self.type != "L":
            assert self.left_child is not None and self.right_child is not None
            self.left_child.reset()
            self.right_child.reset()

    def to_nnf(self) -> aria_nnf.NNF:
        """Convert this DNNF node to the richer ``aria.bool.nnf`` representation."""
        if self.type == "L":
            if self.constant_value is True:
                return aria_nnf.true
            if self.constant_value is False:
                return aria_nnf.false
            assert self._literal_value is not None
            literal = int(self._literal_value)
            return aria_nnf.Var(abs(literal), literal > 0)
        assert self.left_child is not None and self.right_child is not None
        left = self.left_child.to_nnf()
        right = self.right_child.to_nnf()
        if self.type == "A":
            return aria_nnf.And({left, right}).simplify()
        return aria_nnf.Or({left, right}).simplify()


class DNNF_Compiler:
    """Compiler for converting CNF to DNNF."""

    def __init__(self, dtree: Node) -> None:
        self.dtree = dtree
        self.cache: Dict[Tuple[FormulaState, Tuple[int, ...], str], DNF_Node] = {}
        self.cache_lit: Dict[int, DNF_Node] = {}
        self.boolean_cache: Dict[bool, DNF_Node] = {}
        self.ddnnf: Optional[DNF_Node] = None
        self._default_atoms = sorted(set(dtree.atoms))

    def _make_literal_node(self, literal: int) -> DNF_Node:
        if literal not in self.cache_lit:
            self.cache_lit[literal] = DNF_Node(node_type="L", literal=literal)
        return self.cache_lit[literal]

    def create_boolean_node(self, value: bool) -> DNF_Node:
        """Create a shared boolean constant leaf."""
        if value not in self.boolean_cache:
            self.boolean_cache[value] = DNF_Node(node_type="L", literal=value)
        return self.boolean_cache[value]

    def compose(
        self,
        node_type: str,
        list_tree: List[Optional[DNF_Node]],
        conflict: Optional[List[int]] = None,
    ) -> Optional[DNF_Node]:
        """
        Compose nodes into a right-associated binary tree with simplification.
        """
        if node_type == "L":
            raise ValueError("compose does not create literal nodes")

        nodes = [node for node in list_tree if node is not None]
        if not nodes:
            return None

        if node_type == "A":
            filtered: List[DNF_Node] = []
            for node in nodes:
                if node.is_boolean_leaf():
                    if node.literal is False:
                        return self.create_boolean_node(False)
                    continue
                filtered.append(node)
            if not filtered:
                return self.create_boolean_node(True)
            nodes = filtered
        else:
            filtered = []
            for node in nodes:
                if node.is_boolean_leaf():
                    if node.literal is True:
                        return self.create_boolean_node(True)
                    continue
                filtered.append(node)
            if not filtered:
                return self.create_boolean_node(False)
            nodes = filtered

        if len(nodes) == 1:
            return nodes[0]

        if conflict is not None:
            if len(conflict) != len(nodes):
                raise ValueError("Conflict labels must match the number of OR branches")
            current = nodes[-1]
            for index in range(len(nodes) - 2, -1, -1):
                current = DNF_Node(
                    node_type=node_type,
                    left_child=nodes[index],
                    right_child=current,
                    conflict_atom=abs(conflict[index]),
                )
            return current

        current = nodes[-1]
        for node in reversed(nodes[:-1]):
            current = DNF_Node(node_type=node_type, left_child=node, right_child=current)
        return current

    def create_term_node(self, term: List[int]) -> Optional[DNF_Node]:
        """Create a conjunction node from a list of literals."""
        normalized = []
        seen: Set[int] = set()
        for literal in term:
            if -literal in seen:
                return self.create_boolean_node(False)
            if literal not in seen:
                seen.add(literal)
                normalized.append(literal)
        leaves = [self._make_literal_node(literal) for literal in normalized]
        return self.compose(node_type="A", list_tree=leaves)

    def _normalize_formula(self, clauses: Sequence[Sequence[int]]) -> FormulaState:
        normalized: List[Clause] = []
        for clause in clauses:
            if len(clause) == 0:
                normalized.append(tuple())
                continue
            deduped = sorted(set(int(lit) for lit in clause), key=lambda lit: (abs(lit), lit))
            clause_set = set(deduped)
            if any(-lit in clause_set for lit in deduped):
                continue
            normalized.append(tuple(deduped))
        normalized.sort()
        return tuple(normalized)

    def _bcp_formula(
        self, formula: Sequence[Sequence[int]], literal: int
    ) -> Union[FormulaState, int]:
        modified: List[Clause] = []
        for clause in formula:
            clause_set = set(clause)
            if literal in clause_set:
                continue
            if -literal in clause_set:
                reduced = tuple(lit for lit in clause if lit != -literal)
                if len(reduced) == 0:
                    return -1
                modified.append(reduced)
            else:
                modified.append(tuple(clause))
        return self._normalize_formula(modified)

    def bcp(self, dtree: Node, literal: int) -> Union[Node, int]:
        """
        Perform Boolean Constraint Propagation on the given dtree with the given literal.
        """
        reduced = self._bcp_formula(tuple(tuple(clause) for clause in dtree.clauses), literal)
        if reduced == -1:
            return -1
        return self._build_residual_dtree(reduced)

    def _build_residual_dtree(self, formula: FormulaState) -> Node:
        leaves = [Node(node_id=index, clause=list(clause)) for index, clause in enumerate(formula)]
        if not leaves:
            return Node(node_id=0, clause=[])
        current = leaves[-1]
        next_id = len(leaves)
        for leaf in reversed(leaves[:-1]):
            current = Node(node_id=next_id, left_child=leaf, right_child=current)
            next_id += 1
        return current

    def unit_propagation(self, dtree: Node) -> Tuple[Union[Node, int], List[int]]:
        """Perform unit propagation on a dtree by using its clause set."""
        formula = self._normalize_formula(dtree.clauses)
        reduced, assignments = self._unit_propagation_formula(formula)
        if reduced == -1:
            return -1, []
        return self._build_residual_dtree(reduced), assignments

    def _unit_propagation_formula(
        self, formula: FormulaState
    ) -> Tuple[Union[FormulaState, int], List[int]]:
        current = formula
        assignments: List[int] = []
        assignment_set: Set[int] = set()
        while True:
            unit_literals = []
            for clause in current:
                if len(clause) == 0:
                    return -1, []
                if len(clause) == 1:
                    unit_literals.append(clause[0])
            if not unit_literals:
                return current, assignments
            for literal in unit_literals:
                if -literal in assignment_set:
                    return -1, []
                if literal in assignment_set:
                    continue
                assignment_set.add(literal)
                assignments.append(literal)
                current = self._bcp_formula(current, literal)
                if current == -1:
                    return -1, []

    def _formula_atoms(self, formula: FormulaState) -> List[int]:
        return sorted({abs(lit) for clause in formula for lit in clause})

    def clause2ddnnf(self, dtree: Node) -> Optional[DNF_Node]:
        """
        Convert a single clause dtree leaf to DNNF.
        """
        if not dtree.clauses:
            return self.create_boolean_node(True)
        clause = dtree.clauses[0]
        if len(clause) == 0:
            return self.create_boolean_node(False)
        nodes: List[DNF_Node] = []
        conflict: List[int] = []
        for i, literal in enumerate(clause):
            literals = [self._make_literal_node(literal)]
            literals.extend(self._make_literal_node(-clause[j]) for j in range(i))
            choice = self.compose(node_type="A", list_tree=literals)
            assert choice is not None
            nodes.append(choice)
            conflict.append(literal)
        return self.compose(node_type="O", list_tree=nodes, conflict=conflict)

    def _choose_split_variable(
        self,
        formula: FormulaState,
        preferred_atoms: Optional[Iterable[int]] = None,
        strategy: str = "separator_frequency",
    ) -> int:
        counts: Dict[int, int] = {}
        for clause in formula:
            for literal in clause:
                var = abs(literal)
                counts[var] = counts.get(var, 0) + 1
        if not counts:
            raise ValueError("Cannot choose a split variable for an empty formula")
        if strategy == "first":
            return min(counts)
        if preferred_atoms is not None and strategy in ("separator_frequency", "frequency"):
            preferred = [var for var in preferred_atoms if var in counts]
            if preferred:
                return max(preferred, key=lambda var: (counts[var], -var))
        if strategy in ("separator_frequency", "frequency"):
            return max(counts, key=lambda var: (counts[var], -var))
        if strategy == "appearance":
            for clause in formula:
                for literal in clause:
                    return abs(literal)
        raise ValueError(f"Unknown DNNF split strategy: {strategy}")

    def _compile_formula(
        self,
        formula: FormulaState,
        assumptions: Tuple[int, ...],
        split_strategy: str = "separator_frequency",
    ) -> DNF_Node:
        cache_key = (formula, assumptions, split_strategy)
        cached = self.cache.get(cache_key)
        if cached is not None:
            return cached

        reduced, units = self._unit_propagation_formula(formula)
        if reduced == -1:
            result = self.create_boolean_node(False)
            self.cache[cache_key] = result
            return result

        all_assumptions = tuple(sorted(set(assumptions).union(units), key=lambda lit: (abs(lit), lit)))
        term_node = self.create_term_node(list(units))

        if len(reduced) == 0:
            result = self.compose(node_type="A", list_tree=[term_node]) or self.create_boolean_node(True)
            self.cache[cache_key] = result
            return result

        if len(reduced) == 1:
            clause_node = self.clause2ddnnf(Node(node_id=0, clause=list(reduced[0])))
            result = self.compose(node_type="A", list_tree=[term_node, clause_node])
            assert result is not None
            self.cache[cache_key] = result
            return result

        separator_hint = None
        try:
            if self.dtree.separators:
                separator_hint = self.dtree.separators
        except Exception:
            separator_hint = None
        split_var = self._choose_split_variable(
            reduced, separator_hint, strategy=split_strategy
        )
        pos_reduced = self._bcp_formula(reduced, split_var)
        neg_reduced = self._bcp_formula(reduced, -split_var)

        pos_node = (
            self.create_boolean_node(False)
            if pos_reduced == -1
            else self._compile_formula(
                pos_reduced, all_assumptions + (split_var,), split_strategy=split_strategy
            )
        )
        neg_node = (
            self.create_boolean_node(False)
            if neg_reduced == -1
            else self._compile_formula(
                neg_reduced, all_assumptions + (-split_var,), split_strategy=split_strategy
            )
        )

        pos_branch = self.compose(
            node_type="A",
            list_tree=[self._make_literal_node(split_var), pos_node],
        )
        neg_branch = self.compose(
            node_type="A",
            list_tree=[self._make_literal_node(-split_var), neg_node],
        )
        split_node = self.compose(
            node_type="O",
            list_tree=[pos_branch, neg_branch],
            conflict=[split_var, split_var],
        )
        result = self.compose(node_type="A", list_tree=[term_node, split_node])
        assert result is not None
        self.cache[cache_key] = result
        return result

    def cnf2aux(
        self, dtree: Node, split_strategy: str = "separator_frequency"
    ) -> Optional[DNF_Node]:
        """
        Convert CNF to auxiliary DNNF with caching.
        """
        return self._compile_formula(
            self._normalize_formula(dtree.clauses), tuple(), split_strategy=split_strategy
        )

    def cnf2ddnnf(
        self, dtree: Node, split_strategy: str = "separator_frequency"
    ) -> Optional[DNF_Node]:
        """
        Convert CNF to DNNF.
        """
        return self._compile_formula(
            self._normalize_formula(dtree.clauses), tuple(), split_strategy=split_strategy
        )

    def compile(self, split_strategy: str = "separator_frequency") -> Optional[DNF_Node]:
        """Compile the decision tree to DNNF."""
        self.ddnnf = self.cnf2ddnnf(self.dtree, split_strategy=split_strategy)
        return copy.deepcopy(self.ddnnf)

    def validate(self, dnnf: DNF_Node) -> None:
        """Validate structural invariants recursively."""
        seen: Set[int] = set()

        def walk(node: DNF_Node) -> None:
            node_id = id(node)
            if node_id in seen:
                return
            seen.add(node_id)
            node.validate()
            if node.type != "L":
                assert node.left_child is not None and node.right_child is not None
                walk(node.left_child)
                walk(node.right_child)

        walk(dnnf)

    def is_decomposable(self, dnnf: DNF_Node) -> bool:
        """Check decomposability of all AND nodes."""
        seen: Set[int] = set()

        def walk(node: DNF_Node) -> bool:
            node_id = id(node)
            if node_id in seen:
                return True
            seen.add(node_id)
            if node.type == "L":
                return True
            assert node.left_child is not None and node.right_child is not None
            if node.type == "A":
                if set(node.left_child.atoms).intersection(node.right_child.atoms):
                    return False
            return walk(node.left_child) and walk(node.right_child)

        return walk(dnnf)

    def is_deterministic(self, dnnf: DNF_Node) -> bool:
        """Check determinism using the ``aria.bool.nnf`` semantics."""
        return dnnf.to_nnf().deterministic()

    def is_smooth(self, dnnf: DNF_Node) -> bool:
        """Check smoothness of all OR nodes."""
        seen: Set[int] = set()

        def walk(node: DNF_Node) -> bool:
            node_id = id(node)
            if node_id in seen:
                return True
            seen.add(node_id)
            if node.type == "L":
                return True
            assert node.left_child is not None and node.right_child is not None
            if node.type == "O":
                if sorted(node.left_child.atoms) != sorted(node.right_child.atoms):
                    return False
            return walk(node.left_child) and walk(node.right_child)

        return walk(dnnf)

    def to_nnf(self, dnnf: DNF_Node) -> aria_nnf.NNF:
        """Convert a compiled DNNF into ``aria.bool.nnf``."""
        result = dnnf.to_nnf().simplify()
        if self.is_deterministic(dnnf):
            result.mark_deterministic()
        return result

    def conditioning(self, dnnf: DNF_Node, instanciation: List[int]) -> DNF_Node:
        """Condition a DNNF on a set of literals."""
        assignment = {abs(lit): lit > 0 for lit in instanciation}

        def apply(node: DNF_Node) -> DNF_Node:
            if node.type == "L":
                if isinstance(node.literal, bool):
                    return self.create_boolean_node(bool(node.literal))
                literal = int(node.literal)
                value = assignment.get(abs(literal))
                if value is None:
                    return DNF_Node("L", literal=literal)
                return self.create_boolean_node(value == (literal > 0))
            assert node.left_child is not None and node.right_child is not None
            left = apply(node.left_child)
            right = apply(node.right_child)
            return DNF_Node(
                node.type,
                left_child=left,
                right_child=right,
                conflict_atom=node.conflict_atom,
            )

        return apply(dnnf)

    def conjoin(self, dnnf: DNF_Node, instanciation: List[int]) -> DNF_Node:
        """Conjoin a DNNF with a literal instantiation."""
        conditioned = self.simplify(self.conditioning(copy.deepcopy(dnnf), instanciation))
        term = self.create_term_node(instanciation)
        result = self.compose(node_type="A", list_tree=[conditioned, term])
        assert result is not None
        return result

    def simplify(self, dnnf: DNF_Node) -> DNF_Node:
        """Simplify a DNNF by folding boolean constants."""
        if dnnf.type == "L":
            return dnnf

        assert dnnf.left_child is not None and dnnf.right_child is not None
        left = self.simplify(dnnf.left_child)
        right = self.simplify(dnnf.right_child)

        if dnnf.type == "A":
            if left.is_boolean_leaf() and left.literal is False:
                return self.create_boolean_node(False)
            if right.is_boolean_leaf() and right.literal is False:
                return self.create_boolean_node(False)
            if left.is_boolean_leaf() and left.literal is True:
                return right
            if right.is_boolean_leaf() and right.literal is True:
                return left
            return DNF_Node("A", left_child=left, right_child=right)

        if left.is_boolean_leaf() and left.literal is True:
            return self.create_boolean_node(True)
        if right.is_boolean_leaf() and right.literal is True:
            return self.create_boolean_node(True)
        if left.is_boolean_leaf() and left.literal is False:
            return right
        if right.is_boolean_leaf() and right.literal is False:
            return left
        return DNF_Node("O", left_child=left, right_child=right, conflict_atom=dnnf.conflict_atom)

    def is_sat(self, dnnf: DNF_Node) -> bool:
        """Check if a DNNF is satisfiable."""
        simplified = self.simplify(copy.deepcopy(dnnf))
        if simplified.type == "L":
            if isinstance(simplified.literal, bool):
                return bool(simplified.literal)
            return True
        assert simplified.left_child is not None and simplified.right_child is not None
        if simplified.type == "A":
            return self.is_sat(simplified.left_child) and self.is_sat(simplified.right_child)
        return self.is_sat(simplified.left_child) or self.is_sat(simplified.right_child)

    def project(self, dnnf: DNF_Node, atoms: List[int]) -> DNF_Node:
        """Project a DNNF onto a set of atoms by existentially forgetting others."""
        keep = set(atoms)

        def apply(node: DNF_Node) -> DNF_Node:
            if node.type == "L":
                if isinstance(node.literal, bool):
                    return self.create_boolean_node(bool(node.literal))
                if abs(int(node.literal)) not in keep:
                    return self.create_boolean_node(True)
                return DNF_Node("L", literal=int(node.literal))
            assert node.left_child is not None and node.right_child is not None
            return DNF_Node(
                node.type,
                left_child=apply(node.left_child),
                right_child=apply(node.right_child),
                conflict_atom=node.conflict_atom,
            )

        return apply(dnnf)

    def m_card(self, dnnf: DNF_Node) -> float:
        """Compute the minimum number of negated literals needed in a model."""
        if dnnf.type == "L":
            if isinstance(dnnf.literal, bool):
                return 0.0 if dnnf.literal else float("inf")
            return 0.0 if int(dnnf.literal) > 0 else 1.0
        assert dnnf.left_child is not None and dnnf.right_child is not None
        if dnnf.type == "O":
            return min(self.m_card(dnnf.left_child), self.m_card(dnnf.right_child))
        return self.m_card(dnnf.left_child) + self.m_card(dnnf.right_child)

    def minimize(self, dnnf: DNF_Node) -> Optional[DNF_Node]:
        """Keep only minimum-cardinality OR branches."""
        if dnnf.type == "L":
            return dnnf
        assert dnnf.left_child is not None and dnnf.right_child is not None
        left = self.minimize(dnnf.left_child)
        right = self.minimize(dnnf.right_child)
        if dnnf.type == "A":
            return self.compose(node_type="A", list_tree=[left, right])
        left_cost = self.m_card(left) if left is not None else float("inf")
        right_cost = self.m_card(right) if right is not None else float("inf")
        if left_cost < right_cost:
            return left
        if right_cost < left_cost:
            return right
        return self.compose(
            node_type="O",
            list_tree=[left, right],
            conflict=[dnnf.conflict_atom or 0, dnnf.conflict_atom or 0],
        )

    def create_trivial_node(self, atom: int) -> DNF_Node:
        """Create a tautological OR node over one atom."""
        return DNF_Node(
            "O",
            left_child=self._make_literal_node(atom),
            right_child=self._make_literal_node(-atom),
            conflict_atom=abs(atom),
        )

    def smooth(self, dnnf: DNF_Node) -> DNF_Node:
        """Smooth a DNNF so OR branches mention the same atom set."""
        if dnnf.type == "L":
            return dnnf
        assert dnnf.left_child is not None and dnnf.right_child is not None
        left = self.smooth(dnnf.left_child)
        right = self.smooth(dnnf.right_child)
        if dnnf.type == "A":
            return DNF_Node("A", left_child=left, right_child=right)

        atoms = sorted(set(left.atoms).union(right.atoms))
        left_missing = sorted(set(atoms).difference(left.atoms))
        right_missing = sorted(set(atoms).difference(right.atoms))
        if left_missing:
            left = self.compose(
                node_type="A",
                list_tree=[left] + [self.create_trivial_node(atom) for atom in left_missing],
            ) or self.create_boolean_node(True)
        if right_missing:
            right = self.compose(
                node_type="A",
                list_tree=[right] + [self.create_trivial_node(atom) for atom in right_missing],
            ) or self.create_boolean_node(True)
        return DNF_Node("O", left_child=left, right_child=right, conflict_atom=dnnf.conflict_atom)

    def _enumerate_models_dicts(self, dnnf: DNF_Node) -> List[Dict[int, bool]]:
        if dnnf.type == "L":
            if isinstance(dnnf.literal, bool):
                return [{}] if dnnf.literal else []
            literal = int(dnnf.literal)
            return [{abs(literal): literal > 0}]

        assert dnnf.left_child is not None and dnnf.right_child is not None
        if dnnf.type == "O":
            models = self._enumerate_models_dicts(dnnf.left_child)
            models.extend(self._enumerate_models_dicts(dnnf.right_child))
            unique: Dict[Tuple[Tuple[int, bool], ...], Dict[int, bool]] = {}
            for model in models:
                key = tuple(sorted(model.items()))
                unique[key] = model
            return list(unique.values())

        left_models = self._enumerate_models_dicts(dnnf.left_child)
        right_models = self._enumerate_models_dicts(dnnf.right_child)
        models: Dict[Tuple[Tuple[int, bool], ...], Dict[int, bool]] = {}
        for left in left_models:
            for right in right_models:
                merged = dict(left)
                consistent = True
                for var, value in right.items():
                    if var in merged and merged[var] != value:
                        consistent = False
                        break
                    merged[var] = value
                if consistent:
                    models[tuple(sorted(merged.items()))] = merged
        return list(models.values())

    def enumerate_models(self, dnnf: DNF_Node) -> List[List[int]]:
        """Enumerate all satisfying assignments represented by a DNNF."""
        models = []
        for model in self._enumerate_models_dicts(dnnf):
            literals = [var if value else -var for var, value in sorted(model.items())]
            models.append(literals)
        models.sort()
        return models

    def model_count(self, dnnf: DNF_Node) -> int:
        """Count the models represented by a DNNF exactly."""
        return len(self.enumerate_models(dnnf))

    def one_model(self, dnnf: DNF_Node) -> Optional[List[int]]:
        """Extract one satisfying assignment, if any."""
        models = self.enumerate_models(dnnf)
        if not models:
            return None
        return models[0]
