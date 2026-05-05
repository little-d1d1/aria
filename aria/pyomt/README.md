# Optimization

Optimization and Maximum Satisfiability (MaxSAT) solvers.

## Components

### MaxSAT Solvers
- `maxsmt/base.py`: Base MaxSAT classes
- `maxsmt/core_guided.py`: Core-guided MaxSAT algorithms
- `maxsmt/local_search.py`: Local search MaxSAT
- `maxsmt/z3_optimize.py`: Z3 optimization interface
- `maxsmt/ihs.py`: Instance-based heuristic search

### OMT (Optimization Modulo Theories)
- `omt_solver.py`: Main OMT solver
- `omtarith/`: OMT for arithmetic theories
  - `arith_opt_lp.py`: LP-based optimization
  - `arith_opt_ls.py`: Local search optimization
  - `arith_opt_qsmt.py`: QSMT-based optimization
- `omtbv/`: OMT for bit-vectors
  - `bv_opt_maxsat.py`: MaxSAT-based BV optimization
  - `bv_opt_qsmt.py`: QSMT-based BV optimization
  - `bit_blast_omt_solver.py`: Bit-blasting approach
  - `boxed/`: Boxed optimization variants
- `omtfp/`: OMT for floating-point theories
  - `fp_omt_parser.py`: SMT-LIB parser for FP objectives
  - `fp_opt_iterative_search.py`: Iterative FP search backends (`ls`, `bs`, `ofpbs`)

### Floating-Point OMT Semantics
- FP optimization follows the OFPBS algorithm from the reference paper.
- The dedicated `ofpbs` backend implements the paper's core bitwise search.
- The optional paper enhancements for branching preference and polarity updates are
  intentionally not applied on the current Z3 backend because the Python solver API
  does not expose equivalent per-bit controls.
- Optimization prefers non-NaN models whenever any exist, and returns a NaN value only
  when every feasible model assigns NaN to the objective.
- Among non-NaN values, optimization uses the usual floating-point numeric order, while
  exact IEEE bit patterns are still preserved in rendered results and lexicographic
  pinning steps.

### Floating-Point Pareto Semantics
- FP Pareto optimization compares objective tuples componentwise using the same
  non-NaN-first paper semantics as single-objective optimization.
- A point is Pareto-optimal if no other feasible point is at least as good in every
  objective and strictly better in at least one objective under the per-objective
  direction (`maximize` or `minimize`).
- Pareto results are rendered as lists of objective tuples, and each FP value is
  shown with both a readable form and its exact IEEE bit pattern.

### MSA (Minimal Satisfying Assignment)
- `msa/mistral_msa.py`: Mistral MSA solver
- `msa/mistral_pysmt.py`: PySMT integration

### Utilities
- `omt_parser.py`: OMT problem parser
- `pysmt_utils.py`: PySMT utilities
- `bin_solver.py`: Binary solver wrapper

## Usage

```python
from aria.pyomt import MaxSMTSolver
import z3

solver = MaxSMTSolver()
solver.add_hard_constraint(z3.BoolVal(True))
result = solver.solve()
```
