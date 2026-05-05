# Aria Examples

This directory contains examples demonstrating various applications and functionalities of the aria library across different domains.

## Core API Examples (`aria-api/`)

Comprehensive examples showcasing aria's core capabilities using Z3 expressions:
- **AllSMT**: Enumerate all satisfying models of SMT formulas
- **Model Sampling**: Advanced sampling techniques for solution space exploration
- **Unsat Cores**: Compute unsatisfiable cores and minimal unsatisfiable subsets (MUS)
- **Backbone**: Compute backbone literals (literals true in all models)
- **Quantifier Elimination**: Eliminate quantifiers from formulas
- **Abduction**: Find explanations/hypotheses for implications
- **Model Counting**: Count the number of satisfying models
- **Interpolation**: Compute interpolants between formulas
- **MaxSMT**: Solve Maximum Satisfiability problems
- **SyGuS**: Syntax-guided synthesis of functions
- **Unification**: Term unification and pattern matching (in `aria.smt.unification`)

## Domain-Specific Applications

### Datalog (`aria/datalog/examples/`)
- **Vendored pyDatalog**: small examples for recursive rules, graph queries, and
  Python-object-backed logic programming

### Formal Verification (`pypmt/`)
- **PyPMT**: Python-based predicate modular verification framework
- Various encoders, compilers, and planners for verification tasks

### Probability & Learning (`prob/`)
- Probabilistic reasoning and sampling examples

### Causal Discovery (`cisan/`)
- **CISan**: Runtime verification of causal discovery algorithms using automated conditional independence reasoning
- Implements PC algorithm and variants with SMT-based independence testing
- Research artifact from ICSE 2024 paper

### DSL Development (`pc_dsl/`)
- **Easy Z3 DSL**: Python DSL that simplifies Z3 constraint solving through class-based syntax
- Supports basic types, bit-vectors, strings, arrays, quantifiers, and floating-point numbers
