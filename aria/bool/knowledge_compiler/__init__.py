"""Public helpers for ``aria.bool.knowledge_compiler``."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Optional, Sequence, Tuple, Union

from pysat.formula import CNF

from .dnnf import DNF_Node, DNNF_Compiler
from .dtree import Dtree_Compiler
from .obdd import BDD, BDD_Compiler

ClauseLike = Sequence[int]
CNFLike = Union[Sequence[ClauseLike], CNF]

__all__ = (
    "DNF_Node",
    "DNNF_Compiler",
    "BDD",
    "BDD_Compiler",
    "CompiledDNNF",
    "CompiledOBDD",
    "compile_dnnf",
    "compile_obdd",
)


def _normalize_cnf(cnf: CNFLike) -> List[List[int]]:
    if isinstance(cnf, CNF):
        return [list(clause) for clause in cnf.clauses]
    return [list(clause) for clause in cnf]


def _variables_of_clauses(clauses: Sequence[Sequence[int]]) -> List[int]:
    return sorted({abs(lit) for clause in clauses for lit in clause})


@dataclass
class CompiledDNNF:
    """Public wrapper around a compiled DNNF artifact."""

    compiler: DNNF_Compiler
    root: DNF_Node
    variables: List[int]

    def validate(self) -> None:
        self.compiler.validate(self.root)

    def is_sat(self) -> bool:
        return self.compiler.is_sat(self.root)

    def model_count(self) -> int:
        return self.compiler.model_count(self.root)

    def one_model(self) -> Optional[List[int]]:
        return self.compiler.one_model(self.root)

    def enumerate_models(self) -> List[List[int]]:
        return self.compiler.enumerate_models(self.root)

    def condition(self, literals: Sequence[int]) -> "CompiledDNNF":
        root = self.compiler.simplify(self.compiler.conditioning(self.root, list(literals)))
        return CompiledDNNF(self.compiler, root, list(self.variables))

    def conjoin(self, literals: Sequence[int]) -> "CompiledDNNF":
        root = self.compiler.simplify(self.compiler.conjoin(self.root, list(literals)))
        return CompiledDNNF(self.compiler, root, list(self.variables))

    def project(self, atoms: Iterable[int]) -> "CompiledDNNF":
        keep = sorted({abs(atom) for atom in atoms})
        root = self.compiler.simplify(self.compiler.project(self.root, keep))
        return CompiledDNNF(self.compiler, root, keep)

    def smooth(self) -> "CompiledDNNF":
        return CompiledDNNF(self.compiler, self.compiler.smooth(self.root), list(self.variables))

    def minimize(self) -> "CompiledDNNF":
        minimized = self.compiler.minimize(self.root)
        if minimized is None:
            minimized = self.compiler.create_boolean_node(False)
        return CompiledDNNF(self.compiler, minimized, list(self.variables))

    def is_decomposable(self) -> bool:
        return self.compiler.is_decomposable(self.root)

    def is_deterministic(self) -> bool:
        return self.compiler.is_deterministic(self.root)

    def is_smooth(self) -> bool:
        return self.compiler.is_smooth(self.root)

    def to_nnf(self):
        return self.compiler.to_nnf(self.root)


@dataclass
class CompiledOBDD:
    """Public wrapper around a compiled OBDD artifact."""

    compiler: BDD_Compiler
    root: BDD
    variables: List[int]
    clauses: List[List[int]]
    key_type: str = "cutset"

    def validate(self) -> None:
        self.compiler.validate(self.root)

    def is_sat(self) -> bool:
        return self.compiler.is_sat(self.root)

    def model_count(self) -> int:
        return self.compiler.model_count(self.root)

    def one_model(self) -> Optional[List[int]]:
        models = self.enumerate_models()
        if not models:
            return None
        return models[0]

    def enumerate_models(self) -> List[List[int]]:
        return self.compiler.enumerate_models(self.root, self.variables)

    def condition(self, literals: Sequence[int]) -> "CompiledOBDD":
        normalized = []
        seen = set()
        for literal in literals:
            lit = int(literal)
            if -lit in seen:
                return compile_obdd([[]], ordering=[], key_type=self.key_type)
            if lit not in seen:
                seen.add(lit)
                normalized.append(lit)

        residual: Union[Sequence[Sequence[int]], int] = [list(clause) for clause in self.clauses]
        for literal in normalized:
            residual = self.compiler.bcp(residual, literal) if residual != -1 else -1
        if residual == -1:
            return compile_obdd([[]], ordering=[], key_type=self.key_type)

        remaining_vars = [var for var in self.variables if var not in {abs(lit) for lit in normalized}]
        return compile_obdd(
            [list(clause) for clause in residual],
            ordering=remaining_vars,
            key_type=self.key_type,
        )

    def project(self, atoms: Iterable[int]):
        keep = {abs(atom) for atom in atoms}
        return self.to_nnf().project(keep)

    def forget(self, atoms: Iterable[int]):
        forget = {abs(atom) for atom in atoms}
        return self.to_nnf().forget(forget)

    def to_nnf(self):
        return self.compiler.to_nnf(self.root)


def compile_dnnf(
    cnf: CNFLike,
    ordering: Optional[List[int]] = None,
    ordering_strategy: str = "appearance",
    split_strategy: str = "separator_frequency",
) -> CompiledDNNF:
    """Compile a CNF-like object to a DNNF wrapper."""
    clauses = _normalize_cnf(cnf)
    dtree_compiler = Dtree_Compiler(clauses)
    dtree = dtree_compiler.el2dt(ordering=ordering, strategy=ordering_strategy)
    compiler = DNNF_Compiler(dtree)
    root = compiler.compile(split_strategy=split_strategy)
    if root is None:
        root = compiler.create_boolean_node(False)
    return CompiledDNNF(compiler=compiler, root=root, variables=_variables_of_clauses(clauses))


def compile_obdd(
    cnf: CNFLike,
    ordering: Optional[List[int]] = None,
    ordering_strategy: str = "appearance",
    key_type: str = "cutset",
) -> CompiledOBDD:
    """Compile a CNF-like object to an OBDD wrapper."""
    clauses = _normalize_cnf(cnf)
    dtree_compiler = Dtree_Compiler(clauses)
    variables = ordering or dtree_compiler.default_ordering(strategy=ordering_strategy)
    compiler = BDD_Compiler(len(variables), clauses, variable_order=variables)
    root = compiler.compile(key_type=key_type)
    return CompiledOBDD(
        compiler=compiler,
        root=root,
        variables=list(variables),
        clauses=[list(clause) for clause in clauses],
        key_type=key_type,
    )
