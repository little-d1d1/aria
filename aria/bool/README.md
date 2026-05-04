# Boolean Reasoning Toolkit

A comprehensive collection of tools and algorithms for Boolean satisfiability (SAT), maximum satisfiability (MaxSAT), quantified Boolean formulas (QBF), and related logical reasoning tasks.

## Components

### Core SAT Solvers
- **SAT solvers**: PySAT, Z3, and brute force implementations
- **MaxSAT solvers**: Multiple algorithms including FM, LSU, RC2, Anytime
- **QBF solvers**: Support for QDIMACS and QCIR formats

### Formula Manipulation
- **CNF simplification**: Tautology elimination, subsumption, blocked clause removal
- **Tseitin transformation**: DNF to CNF conversion with auxiliary variables
- **NNF (Negation Normal Form)**: Full manipulation and reasoning capabilities

### Advanced Features
- **Dissolve**: Distributed SAT solver based on Stålmarck's method with dilemma splits
- **Feature extraction**: SATzilla-style features for SAT instance analysis
- **Knowledge compilation**: DNNF, OBDD compilation from logical formulas
- **Boolean interpolation**: Proof-based and core-based algorithms
- **Boolean backbone**: multiple SAT-level algorithms for implied literal extraction
- **Modal logic**: finite Kripke semantics, parsing, normalization, model utilities, bounded witness search
- **Prime implicants / implicates**: SAT-based enumeration of minimal terms and clauses
- **Three-valued logic**: strong/weak Kleene and related propositional reasoning helpers

### Usage

```python
# SAT solving
from aria.bool.sat.pysat_solver import PySATSolver
solver = PySATSolver()
result = solver.solve(cnf_formula)

# MaxSAT solving
from aria.bool.maxsat import MaxSATSolver
maxsat_solver = MaxSATSolver()
result = maxsat_solver.solve(weighted_cnf)

# CNF simplification
from aria.bool.cnf_simplify import parse_dimacs, write_dimacs
cnf = parse_dimacs("input.cnf")
simplified = cnf.tautology_elimination()
write_dimacs(simplified, "output.cnf")

# Tseitin transformation
from aria.bool.tseitin_converter import tseitin
cnf_result = tseitin(dnf_formula)

# Prime implicants / implicates
from aria.bool.prime import enumerate_prime_implicants, enumerate_prime_implicates
prime_implicants = enumerate_prime_implicants(CNF(from_clauses=[[1, 2], [-1, 3]]))
prime_implicates = enumerate_prime_implicates(CNF(from_clauses=[[1, 2], [-1, 3]]))

# Backbone literals
from aria.bool.backbone import compute_backbone
backbone, calls = compute_backbone(CNF(from_clauses=[[1, 2], [-1, 3], [-2, 3]]))

# Knowledge compilation
from aria.bool.knowledge_compiler import compile_dnnf, compile_obdd

compiled_dnnf = compile_dnnf([[1, 2], [-1, 3]])
compiled_obdd = compile_obdd([[1, 2], [-1, 3]], ordering=[1, 2, 3])
```

## Knowledge Compiler

`aria.bool.knowledge_compiler` provides two exact compiled backends over CNF-like inputs
(`list[list[int]]` or `pysat.formula.CNF`):

- `compile_dnnf(...)` returns a `CompiledDNNF`
- `compile_obdd(...)` returns a `CompiledOBDD`

Both wrappers support:

- `validate()`: structural invariant checks
- `is_sat()`: exact satisfiability of the compiled theory
- `model_count()`: exact model counting for the wrapper's variable domain
- `one_model()`: one satisfying assignment if any
- `to_nnf()`: convert to `aria.bool.nnf` for richer downstream reasoning

`CompiledDNNF` also supports:

- `enumerate_models()`: exact model enumeration as literal lists
- `condition(literals)`: substitution-style conditioning
- `conjoin(literals)`: conjoin unit literals with the theory
- `project(atoms)`: existentially forget all other atoms
- `smooth()`: smooth OR nodes
- `minimize()`: keep minimum-cardinality OR branches
- `is_decomposable()`, `is_deterministic()`, `is_smooth()`

`CompiledOBDD` additionally supports:

- `enumerate_models()`: exact full-model enumeration over the wrapper's `variables`
- `condition(literals)`: exact conditioning by recompiling the residual CNF over the remaining variables
- `project(atoms)` / `forget(atoms)`: via the `aria.bool.nnf` bridge

Heuristic knobs:

- `compile_dnnf(..., ordering_strategy="appearance"|"frequency", split_strategy="separator_frequency"|"frequency"|"appearance"|"first")`
- `compile_obdd(..., ordering=[...])` or `ordering_strategy="appearance"|"frequency"`

When to prefer each backend:

- Use DNNF when you want broader query support inside `knowledge_compiler`, especially projection, smoothing, or minimization.
- Use OBDD when you want an ordered decision-diagram view, exact full-model enumeration over a chosen variable order, or a deterministic bridge into `aria.bool.nnf`.

Exactness notes:

- DNNF model enumeration/counting operates on the compiled DNNF representation and returns the satisfying assignments represented by that artifact.
- OBDD model counting and enumeration are exact over the wrapper's `variables` list, including variables that became irrelevant and are skipped by reduced nodes.

## Submodules

- `cnfsimplifier/`: Advanced CNF manipulation and simplification (optional Rust backend in `cnfsimplifier_rs/`)
- `dissolve/`: Distributed SAT solving with dilemma rules
- `features/`: SAT instance feature extraction and analysis
- `interpolant/`: Boolean interpolation algorithms
- `knowledge_compiler/`: Knowledge compilation to DNNF/OBDD
- `maxsat/`: Maximum satisfiability solvers
- `modal/`: finite-model modal reasoning and bounded countermodel search
- `nnf/`: Negation normal form reasoning
- `backbone/`: Boolean backbone computation
- `prime/`: Prime implicant and prime implicate enumeration
- `threeval/`: three-valued propositional semantics, parsing, and reasoning
- `qbf/`: Quantified Boolean formula support
- `sat/`: Core SAT solver implementations
