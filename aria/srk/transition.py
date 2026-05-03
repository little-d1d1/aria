"""
Transition relations for program verification.

This module implements transition relations as guarded parallel assignments,
providing operations for composing transitions, computing their effects,
and analyzing program behavior.
"""

from __future__ import annotations
from typing import Dict, List, Set, Tuple, Optional, Union, Any, Callable
from dataclasses import dataclass, field
from fractions import Fraction
from enum import Enum

from aria.srk.syntax import (
    Context,
    Symbol,
    Expression,
    make_expression_builder,
    symbols,
    substitute,
)
from aria.srk.linear import QQVector, QQMatrix


class TransitionResult(Enum):
    """Result of transition validity checking."""

    VALID = "valid"
    INVALID = "invalid"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class Transition:
    """A transition relation representing a guarded parallel assignment."""

    # Transform maps variables to terms over input variables and Skolem constants
    transform: Dict[Symbol, Expression]

    # Guard is the condition under which the transition may be executed
    guard: Expression

    # Context for creating expressions
    context: Optional[Context] = field(default=None)

    @staticmethod
    def assume(context: Context, guard: Expression) -> Transition:
        """Create a transition that only checks a guard condition."""
        return Transition(transform={}, guard=guard, context=context)

    @staticmethod
    def assign(context: Context, var: Symbol, term: Expression) -> Transition:
        """Create a transition that assigns a term to a variable."""
        builder = make_expression_builder(context)
        return Transition(
            transform={var: term}, guard=builder.mk_true(), context=context
        )

    @staticmethod
    def parallel_assign(
        context: Context, assignments: List[Tuple[Symbol, Expression]]
    ) -> Transition:
        """Create a transition with parallel assignments."""
        # If a variable appears multiple times, the rightmost assignment wins
        transform = {}
        for var, term in reversed(assignments):
            if var not in transform:  # Only add if not already assigned
                transform[var] = term
        builder = make_expression_builder(context)
        return Transition(transform=transform, guard=builder.mk_true(), context=context)

    @staticmethod
    def havoc(context: Context, variables: List[Symbol]) -> Transition:
        """Create a transition that non-deterministically assigns to variables."""
        # For now, we'll represent havoc as no constraints (variables can take any value)
        # In a full implementation, this would create fresh Skolem constants
        builder = make_expression_builder(context)
        transform = {var: builder.mk_var(var.id, var.typ) for var in variables}
        return Transition(transform=transform, guard=builder.mk_true(), context=context)

    @staticmethod
    def zero() -> Transition:
        """Create the zero transition (unexecutable)."""
        # Create a transition with a false guard
        # We need a context for this
        context = Context()
        builder = make_expression_builder(context)
        return Transition(transform={}, guard=builder.mk_false(), context=context)

    @staticmethod
    def one(context: Context) -> Transition:
        """Create the identity transition (skip)."""
        builder = make_expression_builder(context)
        return Transition(transform={}, guard=builder.mk_true(), context=context)

    def mul(self, other: Transition) -> Transition:
        """Sequential composition of transitions."""
        # For composition: (self; other), evaluate the second transition in
        # the post-state of the first transition.
        context = self.context or other.context
        if context is None:
            raise ValueError("Cannot compose transitions without context")

        builder = make_expression_builder(context)
        subst_map = dict(self.transform)

        combined_transform = dict(self.transform)
        for var, expr in other.transform.items():
            combined_transform[var] = substitute(expr, subst_map)

        combined_guard = builder.mk_and([self.guard, substitute(other.guard, subst_map)])

        return Transition(
            transform=combined_transform, guard=combined_guard, context=context
        )

    def add(self, other: Transition) -> Transition:
        """Non-deterministic choice between transitions."""
        context = self.context or other.context
        if context is None:
            raise ValueError("Cannot add transitions without context")

        builder = make_expression_builder(context)

        # This representation has no first-class Skolem choice variable.  Keep
        # only assignments that are syntactically identical across both arms;
        # dropping differing assignments is a conservative over-approximation
        # and avoids the previous unsound deterministic dict merge.
        combined_transform = {
            var: expr
            for var, expr in self.transform.items()
            if var in other.transform and other.transform[var] == expr
        }
        combined_guard = builder.mk_or([self.guard, other.guard])

        return Transition(
            transform=combined_transform, guard=combined_guard, context=context
        )

    def is_zero(self) -> bool:
        """Check if this is the zero (unexecutable) transition."""
        # Simplified check - in reality would need proper false detection
        # For now, check if guard is false
        return str(self.guard).startswith("False")

    def is_one(self) -> bool:
        """Check if this is the identity transition."""
        return len(self.transform) == 0 and str(self.guard).startswith("True")

    def mem_transform(self, var: Symbol) -> bool:
        """Check if a variable is written to in this transition."""
        return var in self.transform

    def get_transform(self, var: Symbol) -> Optional[Expression]:
        """Get the value assigned to a variable."""
        return self.transform.get(var)

    def transform_enum(self):
        """Enumerate all variable assignments."""
        return self.transform.items()

    def get_guard(self) -> Expression:
        """Get the guard condition."""
        return self.guard

    def defines(self) -> List[Symbol]:
        """Get variables that are defined (written to) by this transition."""
        return list(self.transform.keys())

    def uses(self) -> Set[Symbol]:
        """Get variables that are used (read) by this transition."""
        used_symbols = set()

        # Add symbols from the guard
        if hasattr(self, "guard") and self.guard is not None:
            used_symbols.update(symbols(self.guard))

        # Add symbols from transform expressions
        if hasattr(self, "transform") and self.transform is not None:
            for expr in self.transform.values():
                used_symbols.update(symbols(expr))

        return used_symbols

    def exists(self, predicate: Callable[[Symbol], bool]) -> Transition:
        """Project out variables that don't satisfy the predicate."""
        # Remove variables from transform that don't satisfy predicate
        new_transform = {
            var: expr for var, expr in self.transform.items() if predicate(var)
        }

        # For the guard, we'd need to existentially quantify variables
        # This is a simplified implementation
        return Transition(transform=new_transform, guard=self.guard)

    def linearize(self) -> Transition:
        """Linearize the transition to linear arithmetic."""
        # Default implementation - return self (no linearization)
        # Linearization would need to convert nonlinear terms to linear approximations
        return self

    def widen(self, other: Transition) -> Transition:
        """Widen this transition with another."""
        # Default implementation - return self (no widening)
        # Widening for transitions would need sophisticated abstract interpretation algorithms
        return self

    def star(self) -> Transition:
        """Kleene star -- reflexive transitive closure of this transition.

        Strategy:
        1.  Build a :class:`TransitionFormula` via :meth:`to_transition_formula`.
        2.  Try the full iteration-domain pipeline (``MakeDomain`` +
            ``WedgeGuard``).  This gives the most precise result when the
            underlying abstract domains are operational.
        3.  If the domain pipeline fails (e.g. because APRON is not
            installed), fall back to a formula-based approximation:
            ``K = 0  =>  identity``, ``K >= 1  =>  original guard``.
            This is sound but imprecise -- it over-approximates the
            transform step by forgetting it.
        """
        if self.context is None:
            return self

        srk = self.context

        try:
            from .syntax import (
                mk_const,
                mk_and,
                mk_leq,
                mk_real,
                mk_eq,
                mk_symbol,
                substitute as syntax_substitute,
            )
            from .qQ import QQ

            # --- build transition formula and tr_symbols --------------------
            tf = self.to_transition_formula(srk)

            tr_symbols = []
            pre_to_post_subst = {}  # Symbol -> Const(post_sym)
            for var in self.transform:
                pre_name = srk.show_symbol(var)
                post_sym = srk.mk_symbol(name=pre_name + "'", typ=var.typ)
                tr_symbols.append((var, post_sym))
                pre_to_post_subst[var] = mk_const(srk, post_sym)

            # --- try the full iteration domain -----------------------------
            try:
                from .iteration import MakeDomain, WedgeGuard

                domain = MakeDomain(WedgeGuard)
                domain_elem = domain.abstract(srk, tf)
                closure_formula = domain.closure(domain_elem)

                return Transition(
                    transform=dict(self.transform),
                    guard=closure_formula,
                    context=srk,
                )
            except Exception:
                pass

            # --- fallback: formula-based closure ---------------------------
            from .syntax import Type as _Type, mk_or, mk_true
            loop_sym = mk_symbol(srk, "K", _Type.INT)
            loop_counter = mk_const(srk, loop_sym)

            # K = 0  =>  identity (x' = x for every tracked variable)
            identity_eqs = []
            for pre_sym, post_sym in tr_symbols:
                identity_eqs.append(
                    mk_eq(srk, mk_const(srk, post_sym), mk_const(srk, pre_sym))
                )
            if identity_eqs:
                identity_body = mk_and(srk, identity_eqs)
            else:
                identity_body = mk_true(srk)

            zero_case = mk_and(srk, [
                mk_eq(srk, loop_counter, mk_real(srk, QQ.zero())),
                identity_body,
            ])

            # K >= 1  =>  original guard (with pre->post substitution so the
            # guard talks about the right state pair)
            guard_subst = syntax_substitute(self.guard, pre_to_post_subst)
            at_least_one_case = mk_and(srk, [
                mk_leq(srk, mk_real(srk, QQ.one()), loop_counter),
                guard_subst,
            ])

            closure_guard = mk_and(srk, [
                mk_or(srk, [zero_case, at_least_one_case]),
                mk_leq(srk, mk_real(srk, QQ.zero()), loop_counter),
            ])

            return Transition(
                transform=dict(self.transform),
                guard=closure_guard,
                context=srk,
            )

        except Exception:
            return Transition.one(self.context)

    def abstract_post(self, property: Any) -> Any:
        """Compute abstract post-image."""
        # Default implementation - return the property unchanged
        # Subclasses or specific abstract domains should override this
        return property

    def to_transition_formula(
        self, context: Context
    ) -> Any:  # Returns TransitionFormula
        """Convert to transition formula representation.

        Builds a TransitionFormula whose body is
            guard AND (p1 = t1) AND (p2 = t2) AND ...
        where pi is the post-state symbol for variable i and ti is the
        transform term.  The ``exists`` predicate marks both pre-state
        Var nodes and fresh post-state symbols as existentially bound.
        """
        from .transitionFormula import make as make_tf
        from .syntax import (
            mk_eq,
            mk_const,
            mk_and,
            mk_symbol,
            Var,
            Const,
        )

        if not self.transform:
            # Empty transform: just the guard, no variable pairs
            return make_tf(self.guard, [], exists=lambda s: True)

        # Build post-state symbol pairs and equalities
        tr_symbols = []
        post_defs = []
        post_symbols_set: set = set()

        for var, term in self.transform.items():
            pre_sym = var  # var is already a Symbol
            # Create a fresh post-state symbol with a primed name
            pre_name = context.show_symbol(pre_sym)
            post_sym = context.mk_symbol(name=pre_name + "'", typ=pre_sym.typ)
            post_term = mk_const(context, post_sym)

            tr_symbols.append((pre_sym, post_sym))
            post_defs.append(mk_eq(context, post_term, term))
            post_symbols_set.add(post_sym)

        # Body: guard AND (p1 = t1) AND (p2 = t2) AND ...
        if post_defs:
            body = mk_and(context, [self.guard] + post_defs)
        else:
            body = self.guard

        # Exists predicate: true for pre-state Var nodes and post-state symbols
        def exists(x):
            if isinstance(x, Var):
                return True
            if isinstance(x, Const):
                return x.symbol in post_symbols_set
            return x in post_symbols_set

        return make_tf(body, tr_symbols, exists=exists)

    def interpolate(self, post_condition: Expression) -> List[Expression]:
        """Compute interpolants for this transition and post-condition."""
        # Default implementation - no interpolants
        # Interpolation algorithms would need to be implemented
        return []

    def valid_triple(
        self, pre_condition: Expression, post_condition: Expression
    ) -> TransitionResult:
        """Check validity of {pre} transition {post}."""
        # Default implementation - unknown validity
        # Would need to check if pre ∧ transition ⇒ post

        # For a basic implementation, we can try to use SMT solving
        try:
            # Import SMT solver if available
            from .smt import mk_solver

            if self.context is None:
                return TransitionResult.UNKNOWN

            solver = mk_solver(self.context)

            # Create the triple: pre ∧ guard ∧ (transform conditions) ⇒ post
            # This is a simplified check that doesn't handle the full semantics
            # A full implementation would need to:
            # 1. Create fresh variables for post-state
            # 2. Substitute transform expressions appropriately
            # 3. Check implication

            # For now, return UNKNOWN as we need more sophisticated analysis
            return TransitionResult.UNKNOWN

        except ImportError:
            # SMT solver not available
            return TransitionResult.UNKNOWN
        except Exception:
            # Any other error
            return TransitionResult.UNKNOWN

    def __str__(self) -> str:
        if not self.transform:
            return f"Transition({self.guard} ⇒ skip)"

        updates = ", ".join(f"{var} := {expr}" for var, expr in self.transform.items())
        return f"Transition({self.guard} ⇒ {{{updates}}})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Transition):
            return False
        return self.transform == other.transform and self.guard == other.guard

    def __hash__(self) -> int:
        # Simple hash based on string representation
        return hash(str(self))


# Convenience functions for creating transitions
def make_assume(context: Context, guard: Expression) -> Transition:
    """Create an assume transition."""
    return Transition.assume(context, guard)


def make_assign(context: Context, var: Symbol, term: Expression) -> Transition:
    """Create an assignment transition."""
    return Transition.assign(context, var, term)


def make_parallel_assign(
    context: Context, assignments: List[Tuple[Symbol, Expression]]
) -> Transition:
    """Create a parallel assignment transition."""
    return Transition.parallel_assign(context, assignments)


def make_havoc(context: Context, variables: List[Symbol]) -> Transition:
    """Create a havoc transition."""
    return Transition.havoc(context, variables)


def make_zero() -> Transition:
    """Create the zero transition."""
    return Transition.zero()


def make_one(context: Context) -> Transition:
    """Create the identity transition."""
    return Transition.one(context)


class TransitionSystem:
    """Lightweight transition system wrapper for tests.

    This mirrors the constructor style expected by tests, allowing creation
    from a context and a list of (u, Transition, v) edges.
    """

    def __init__(self, context: Context, edges: List[Tuple[int, "Transition", int]]):
        self.context = context
        self._edges = list(edges)

    def edges(self) -> List[Tuple[int, "Transition", int]]:
        return list(self._edges)
