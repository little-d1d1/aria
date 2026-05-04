"""
OBDD: Ordered Binary Decision Diagrams.
"""

from __future__ import annotations

import copy
from typing import Dict, List, Optional, Sequence, Set, Tuple, Union
from aria.bool import nnf as aria_nnf

Clause = Tuple[int, ...]
FormulaState = Tuple[Clause, ...]


class BDD:
    """Represents a Binary Decision Diagram (BDD) node."""

    def __init__(self, var: int, low: Optional["BDD"], high: Optional["BDD"]) -> None:
        self.var = var
        self.low = low
        self.high = high
        self.explore_id = 0

    def is_sink(self) -> bool:
        """Check if this is a sink node (terminal)."""
        return self.low is None and self.high is None

    def _print_info(
        self, current_id: int, rank: List[List[int]], output_file: Optional[str] = None
    ) -> Tuple[int, List[List[int]]]:
        if self.explore_id > 0:
            return current_id, rank

        if self.is_sink():
            if output_file is not None:
                with open(output_file, "a", encoding="utf-8") as out:
                    if self.var:
                        out.write(
                            f'     {current_id + 1} [label="True", color=green, shape=square];\n'
                        )
                    else:
                        out.write(
                            f'     {current_id + 1} [label="False", color=red, shape=square];\n'
                        )
            else:
                print(f"{current_id + 1}-SINK : {self.var}")
        else:
            assert self.low is not None and self.high is not None
            left_current_id, rank = self.low._print_info(current_id, rank, output_file)
            current_id, rank = self.high._print_info(left_current_id, rank, output_file)
            if output_file is not None:
                with open(output_file, "a", encoding="utf-8") as out:
                    out.write(f'     {current_id + 1} [label="{self.var}"];\n')
                    out.write(
                        f"     {current_id + 1} -> {self.low.explore_id} [style=dotted];\n"
                    )
                    out.write(f"     {current_id + 1} -> {self.high.explore_id};\n")
            else:
                print(f"{current_id + 1}-Var: {self.var}")
        self.explore_id = current_id + 1
        if self.is_sink():
            rank[0].append(self.explore_id)
        else:
            rank[self.var].append(self.explore_id)
        return current_id + 1, rank

    def print_info(
        self, nvars: int, output_file: Optional[str] = None
    ) -> List[List[int]]:
        """Print BDD information."""
        rank = [[] for _ in range(nvars + 1)]
        _, rank = copy.deepcopy(self)._print_info(0, rank, output_file)
        return rank

    def validate(self) -> None:
        """Validate basic BDD node invariants."""
        if self.is_sink():
            return
        if self.low is None or self.high is None:
            raise ValueError("Non-sink BDD nodes must have both low/high branches")
        if self.var <= 0:
            raise ValueError("Non-sink BDD nodes must branch on a positive variable id")


class BDD_Compiler:
    """Compiler for converting CNF to OBDD."""

    def __init__(
        self,
        n_vars: int,
        clausal_form: List[List[int]],
        variable_order: Optional[Sequence[int]] = None,
    ) -> None:
        self.clausal_form = [list(clause) for clause in clausal_form]
        self.variable_order = list(variable_order) if variable_order is not None else list(
            range(1, n_vars + 1)
        )
        self.n_vars = len(self.variable_order)
        self.level_of_var = {
            var: index + 1 for index, var in enumerate(self.variable_order)
        }
        self.unique: Dict[Tuple[int, BDD, BDD], BDD] = {}
        self.cache: Dict[Tuple[int, str, FormulaState], BDD] = {}
        self.f_sink = BDD(False, None, None)
        self.t_sink = BDD(True, None, None)

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

    def bcp(self, formula: Sequence[Sequence[int]], literal: int) -> Union[FormulaState, int]:
        """Boolean Constraint Propagation."""
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

    def _compute_cutset(self, clausal_form: Sequence[Sequence[int]], var: int) -> List[int]:
        """Compute cutset clause indices for a variable in the current residual formula."""
        cutset = []
        for i, clause in enumerate(clausal_form):
            if len(clause) == 0:
                continue
            atoms = [abs(lit) for lit in clause]
            if min(atoms) <= var < max(atoms):
                cutset.append(i)
        return cutset

    def compute_cutset_key(self, clausal_form: Sequence[Sequence[int]], var: int) -> int:
        """Compute a cutset key from the current residual formula."""
        cutset_key = 0
        for i, clause_index in enumerate(self._compute_cutset(clausal_form, var)):
            if len(clausal_form[clause_index]) == 0:
                cutset_key += 2**i
            else:
                cutset_key += hash(clausal_form[clause_index]) & ((1 << (i + 1)) - 1)
        return cutset_key

    def _compute_separator(
        self, clausal_form: Sequence[Sequence[int]], var: int
    ) -> List[int]:
        """Compute the separator variables for a variable in the current residual formula."""
        sep = set()
        for clause_index in self._compute_cutset(clausal_form, var):
            for literal in clausal_form[clause_index]:
                if abs(literal) <= var:
                    sep.add(abs(literal))
        return sorted(sep)

    def compute_separator_key(self, clausal_form: Sequence[Sequence[int]], var: int) -> int:
        """Compute a separator key from the current residual formula."""
        sep_key = 0
        for variable in self._compute_separator(clausal_form, var):
            sep_key += 2**variable
        return sep_key

    def get_nodes(self, var: int, low: BDD, high: BDD) -> BDD:
        """Get or create a reduced BDD node."""
        if low == high:
            return low
        key = (var, low, high)
        if key not in self.unique:
            self.unique[key] = BDD(var, low, high)
        return self.unique[key]

    def _formula_empty(self, clausal_form: FormulaState) -> bool:
        return len(clausal_form) == 0

    def _formula_unsat(self, clausal_form: FormulaState) -> bool:
        return any(len(clause) == 0 for clause in clausal_form)

    def cnf2obdd(
        self, clausal_form: Union[Sequence[Sequence[int]], int], i: int, key_type: str = "cutset"
    ) -> BDD:
        """Convert CNF to OBDD."""
        if key_type not in ("cutset", "separator"):
            raise ValueError("key_type must be 'cutset' or 'separator'")

        if clausal_form == -1:
            return self.f_sink
        formula = self._normalize_formula(clausal_form)
        if self._formula_unsat(formula):
            return self.f_sink
        if self._formula_empty(formula):
            return self.t_sink
        if i > self.n_vars:
            return self.f_sink
        branch_var = self.variable_order[i - 1]

        state_key = (i, key_type, formula)
        cached = self.cache.get(state_key)
        if cached is not None:
            return cached

        if key_type == "cutset":
            _ = self.compute_cutset_key(formula, branch_var)
        else:
            _ = self.compute_separator_key(formula, branch_var)

        low = self.cnf2obdd(
            self.bcp(formula, -branch_var) if not self._formula_empty(formula) else formula,
            i + 1,
            key_type,
        )
        high = self.cnf2obdd(
            self.bcp(formula, branch_var) if not self._formula_empty(formula) else formula,
            i + 1,
            key_type,
        )
        result = self.get_nodes(branch_var, low, high)
        self.cache[state_key] = result
        return result

    def compile(self, key_type: str = "cutset") -> BDD:
        """Compile a CNF formula to OBDD."""
        return self.cnf2obdd(self.clausal_form, 1, key_type)

    def validate(self, bdd: BDD) -> None:
        """Validate reduced ordered BDD invariants recursively."""
        seen: Set[int] = set()

        def walk(node: BDD, min_var: int) -> None:
            node_id = id(node)
            if node_id in seen:
                return
            seen.add(node_id)
            node.validate()
            if node.is_sink():
                return
            assert node.low is not None and node.high is not None
            current_level = self.level_of_var[node.var]
            if current_level < min_var:
                raise ValueError("BDD variable ordering is inconsistent along a path")
            if node.low == node.high:
                raise ValueError("Reduced BDD nodes cannot have identical children")
            walk(node.low, current_level + 1)
            walk(node.high, current_level + 1)

        walk(bdd, 1)

    def is_sat(self, bdd: BDD) -> bool:
        """Check if the BDD is satisfiable."""
        if bdd.is_sink():
            return bool(bdd.var)
        assert bdd.low is not None and bdd.high is not None
        return self.is_sat(bdd.low) or self.is_sat(bdd.high)

    def condition(self, bdd: BDD, literals: Sequence[int]) -> BDD:
        """Condition a BDD on a set of literals."""
        assignment = {abs(lit): lit > 0 for lit in literals}
        memo: Dict[int, BDD] = {}

        def restrict(node: BDD) -> BDD:
            node_id = id(node)
            cached = memo.get(node_id)
            if cached is not None:
                return cached
            if node.is_sink():
                memo[node_id] = node
                return node
            assert node.low is not None and node.high is not None
            choice = assignment.get(node.var)
            if choice is True:
                result = restrict(node.high)
            elif choice is False:
                result = restrict(node.low)
            else:
                low = restrict(node.low)
                high = restrict(node.high)
                result = self.get_nodes(node.var, low, high)
            memo[node_id] = result
            return result

        return restrict(bdd)

    def one_model(self, bdd: BDD) -> Optional[List[int]]:
        """Extract one satisfying assignment from the BDD."""
        if bdd.is_sink():
            return [] if bdd.var else None
        assert bdd.low is not None and bdd.high is not None
        high_model = self.one_model(bdd.high)
        if high_model is not None:
            return [bdd.var] + high_model
        low_model = self.one_model(bdd.low)
        if low_model is not None:
            return [-bdd.var] + low_model
        return None

    def enumerate_models(
        self, bdd: BDD, variables: Optional[Sequence[int]] = None
    ) -> List[List[int]]:
        """Enumerate full satisfying assignments over the given variable order."""
        if variables is None:
            variables = self.variable_order
        variable_order = list(variables)
        level_of_var = {var: index for index, var in enumerate(variable_order)}

        memo: Dict[Tuple[int, int], List[List[int]]] = {}

        def suffix_assignments(start_index: int) -> List[List[int]]:
            if start_index >= len(variable_order):
                return [[]]
            result = [[]]
            for var in variable_order[start_index:]:
                next_result: List[List[int]] = []
                for assignment in result:
                    next_result.append([var] + assignment)
                    next_result.append([-var] + assignment)
                result = next_result
            return result

        def walk(node: BDD, level_index: int) -> List[List[int]]:
            key = (id(node), level_index)
            cached = memo.get(key)
            if cached is not None:
                return cached
            if node.is_sink():
                result = suffix_assignments(level_index) if node.var else []
                memo[key] = result
                return result

            assert node.low is not None and node.high is not None
            node_index = level_of_var[node.var]
            skipped = variable_order[level_index:node_index]
            skipped_assignments = suffix_assignments(level_index) if node_index == len(variable_order) else None
            del skipped_assignments  # keep structure explicit; skipped handled below

            prefix_choices = [[]]
            for skipped_var in skipped:
                next_prefixes: List[List[int]] = []
                for prefix in prefix_choices:
                    next_prefixes.append(prefix + [skipped_var])
                    next_prefixes.append(prefix + [-skipped_var])
                prefix_choices = next_prefixes

            result: List[List[int]] = []
            for prefix in prefix_choices:
                for suffix in walk(node.low, node_index + 1):
                    result.append(prefix + [-node.var] + suffix)
                for suffix in walk(node.high, node_index + 1):
                    result.append(prefix + [node.var] + suffix)
            memo[key] = result
            return result

        models = walk(bdd, 0)
        models.sort()
        return models

    def model_count(self, bdd: BDD) -> int:
        """Count satisfying assignments represented by the BDD."""
        memo: Dict[Tuple[int, int], int] = {}

        def count(node: BDD, level: int) -> int:
            node_id = (id(node), level)
            cached = memo.get(node_id)
            if cached is not None:
                return cached
            if node.is_sink():
                result = (2 ** (self.n_vars - level + 1)) if node.var else 0
            else:
                assert node.low is not None and node.high is not None
                node_level = self.level_of_var[node.var]
                skipped = max(0, node_level - level)
                multiplier = 2**skipped
                result = multiplier * (
                    count(node.low, node_level + 1) + count(node.high, node_level + 1)
                )
            memo[node_id] = result
            return result

        return count(bdd, 1)

    def to_nnf(self, bdd: BDD) -> aria_nnf.NNF:
        """Convert an OBDD into an equivalent deterministic/decomposable NNF."""
        memo: Dict[int, aria_nnf.NNF] = {}

        def convert(node: BDD) -> aria_nnf.NNF:
            node_id = id(node)
            cached = memo.get(node_id)
            if cached is not None:
                return cached
            if node.is_sink():
                result = aria_nnf.true if node.var else aria_nnf.false
            else:
                assert node.low is not None and node.high is not None
                var = aria_nnf.Var(node.var)
                result = aria_nnf.decision(var, convert(node.high), convert(node.low)).simplify()
                result.mark_deterministic()
            memo[node_id] = result
            return result

        return convert(bdd)
