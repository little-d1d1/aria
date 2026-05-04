"""Solving Exists-Forall Problem (currently focus on bit-vec?).

https://github.com/pysmt/pysmt/blob/97088bf3b0d64137c3099ef79a4e153b10ccfda7/examples/efsmt.py

Possible extensions:
- better generalization for esolver
- better generalization for fsolver
- uniform sampling for processing multiple models each round?
- use unsat core??

However, the counterexample may not be general enough to exclude a large
class of invalid expressions, which will lead to the repetition of several
loop iterations. We believe our sampling technique could be a good
enhancement to CEGIS. By generating several diverse counterexamples, the
verifier can provide more information to the learner so that it can make
more progress on its own, limiting the number of calls to the verifier
"""

import logging
import signal
import time
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Callable, List, cast

import z3

from aria.quant.efbv.efbv_parallel.efbv_exists_solver import ExistsSolver
from aria.quant.efbv.efbv_parallel import efbv_forall_solver
from aria.quant.efbv.efbv_parallel.efbv_forall_solver import ForAllSolver
from aria.quant.efbv.efbv_parallel.efbv_utils import (
    EFBVResult,
    EFBVTactic,
    EFBVSolver,
    FSolverMode,
)
from aria.quant.efbv.efbv_parallel.exceptions import (
    ExitsSolverSuccess,
    ExitsSolverUnknown,
    ForAllSolverSuccess,
    ForAllSolverUnknown,
)

logger = logging.getLogger(__name__)

g_efbv_tactic = EFBVTactic.Z3_QBF


def _contains_quantifier(expr: z3.ExprRef) -> bool:
    """Return True when an expression still contains nested quantifiers."""
    stack = [expr]
    seen = set()
    while stack:
        current = stack.pop()
        key = current.get_id()
        if key in seen:
            continue
        seen.add(key)
        if z3.is_quantifier(current):
            return True
        stack.extend(current.children())
    return False


@dataclass
class CEGISProfile:
    iterations: int = 0
    exists_sampling_sec: float = 0.0
    instantiate_sec: float = 0.0
    forall_check_sec: float = 0.0
    learn_sec: float = 0.0

    def log(self, solver_name: str) -> None:
        logger.info(
            "%s profile: iterations=%d exists_sampling=%.3fs instantiate=%.3fs forall_check=%.3fs learn=%.3fs total=%.3fs",
            solver_name,
            self.iterations,
            self.exists_sampling_sec,
            self.instantiate_sec,
            self.forall_check_sec,
            self.learn_sec,
            self.exists_sampling_sec
            + self.instantiate_sec
            + self.forall_check_sec
            + self.learn_sec,
        )


def _make_parent_cleanup_handler(cleanup: Callable[[], None]):
    def _handle_parent_signal(signum: int, _frame) -> None:
        cleanup()
        raise SystemExit(128 + signum)

    return _handle_parent_signal


@contextmanager
def _parent_pool_cleanup_scope(cleanup: Callable[[], None]):
    previous_handlers = {}
    handler = _make_parent_cleanup_handler(cleanup)
    try:
        for sig_name in ("SIGTERM", "SIGINT", "SIGHUP"):
            sig = getattr(signal, sig_name, None)
            if sig is None:
                continue
            previous_handlers[sig] = signal.getsignal(sig)
            signal.signal(sig, handler)
        yield
    finally:
        for sig, previous in previous_handlers.items():
            signal.signal(sig, previous)


def bv_efsmt_with_uniform_sampling(
    exists_vars,
    forall_vars,
    phi,
    maxloops=None,
    num_samples: int | None = None,
    num_workers: int = 4,
    forall_mode: FSolverMode | None = None,
):
    """
    Solve exists x. forall y. phi(x, y) using uniform sampling.

    Args:
        exists_vars: List of existential variables
        forall_vars: List of universal variables
        phi: Formula to solve
        maxloops: Maximum number of iterations (None for unlimited)
        num_samples: Number of samples to generate per iteration
        num_workers: Worker count for forall checks
        forall_mode: Scheduling mode for forall checks

    Returns:
        EFBVResult indicating SAT/UNSAT/UNKNOWN
    """
    # x = [item for item in get_vars(phi) if item not in y]

    if _contains_quantifier(phi):
        logger.warning(
            "efbv-par expects a quantifier-free EFSMT body; "
            "nested quantifiers remain after parsing, so returning UNKNOWN"
        )
        return EFBVResult.UNKNOWN

    if forall_mode is not None:
        efbv_forall_solver.m_forall_solver_strategy = forall_mode
    if num_samples is None:
        # TODO: revisit whether num_samples should be decoupled from workers once
        # we have profiler data for exists sampling vs. forall checking.
        num_samples = num_workers

    esolver = ExistsSolver(exists_vars, z3.BoolVal(True))
    fsolver = ForAllSolver(
        exists_vars[0].ctx,
        forall_vars=forall_vars,
        num_workers=num_workers,
    )
    # fsolver.vars = forall_vars
    # fsolver.phi = phi

    iterations = 0
    result = EFBVResult.UNKNOWN
    profile = CEGISProfile()
    try:
        with _parent_pool_cleanup_scope(fsolver.terminate):
            while maxloops is None or iterations <= maxloops:
                logger.debug(f"Iteration: {iterations}")
                iterations += 1
                profile.iterations = iterations
                # TODO: need to make the fist and the subsequent iteration different???
                # TODO: in the uniform sampler, I always call the solver once before xx...
                # Get multiple exist models
                phase_start = time.perf_counter()
                e_models = esolver.get_models(num_samples)
                profile.exists_sampling_sec += time.perf_counter() - phase_start

                if len(e_models) == 0:
                    logger.debug("  Success with UNSAT")
                    result = EFBVResult.UNSAT  # esolver tells unsat
                    break
                reverse_sub_phis = []
                phase_start = time.perf_counter()
                for emodel in e_models:
                    x_mappings = [
                        (x, emodel.eval(x, model_completion=True)) for x in exists_vars
                    ]
                    sub_phi = z3.simplify(z3.substitute(phi, x_mappings))
                    reverse_sub_phis.append(z3.Not(sub_phi))
                profile.instantiate_sec += time.perf_counter() - phase_start

                phase_start = time.perf_counter()
                fmodels = fsolver.check(reverse_sub_phis)
                profile.forall_check_sec += time.perf_counter() - phase_start
                if len(fmodels) == 0:
                    logger.debug("  Success with SAT")
                    result = EFBVResult.SAT  # fsolver tells sat
                    break
                phase_start = time.perf_counter()
                for fmodel in fmodels:
                    y_mappings = [
                        (y, fmodel.eval(y, model_completion=True)) for y in forall_vars
                    ]
                    sub_phi = z3.simplify(z3.substitute(phi, y_mappings))
                    if z3.is_false(sub_phi):
                        logger.debug("  Success with UNSAT")
                        raise ExitsSolverSuccess()
                    esolver.fmls.append(cast(z3.BoolRef, sub_phi))
                profile.learn_sec += time.perf_counter() - phase_start

    except ForAllSolverSuccess:
        logger.debug("Forall solver success - SAT")
        result = EFBVResult.SAT
    except ForAllSolverUnknown:
        logger.debug("  Forall solver UNKNOWN")
        result = EFBVResult.UNKNOWN
    except ExitsSolverSuccess:
        logger.debug("Exists solver success - UNSAT")
        result = EFBVResult.UNSAT
    except ExitsSolverUnknown:
        logger.debug("  Exists solver UNKNOWN")
        result = EFBVResult.UNKNOWN
    except Exception as ex:
        logger.error("Unexpected error: %s", ex)
        result = EFBVResult.UNKNOWN
    finally:
        fsolver.close()
        profile.log("efbv")

    return result


class ParallelEFBVSolver(EFBVSolver):
    """Parallel EFBV solver using CEGIS with uniform sampling."""

    def __init__(self, **kwargs):
        """Initialize parallel EFBV solver.

        Args:
            mode: Solver mode (e.g., "canary", "qbf", "simple_cegar", "z3")
        """
        super().__init__(**kwargs)
        self.mode = kwargs.get("mode", "canary")
        self.maxloops = kwargs.get("maxloops", None)
        self.num_workers = kwargs.get("num_workers", 4)
        # TODO: keep default sampling parallelism aligned with worker count so
        # each CEGIS round can actually saturate the configured forall workers.
        self.num_samples = kwargs.get("num_samples", self.num_workers)
        self.forall_mode = kwargs.get("forall_mode", None)

    def solve_efsmt_bv(
        self, existential_vars: List, universal_vars: List, phi: z3.ExprRef
    ):
        """Solve EFBV problem."""
        if self.mode == "canary":
            return bv_efsmt_with_uniform_sampling(
                existential_vars,
                universal_vars,
                phi,
                maxloops=self.maxloops,
                num_samples=self.num_samples,
                num_workers=self.num_workers,
                forall_mode=self.forall_mode,
            )
        raise NotImplementedError()


def test_efsmt():
    """Test function for EFBV solver."""
    x, y, z = z3.BitVecs("x y z", 16)
    fmla = z3.Implies(z3.And(y > 0, y < 10), y - 2 * x < 7)
    #
    start = time.time()
    solver = ParallelEFBVSolver(mode="canary")
    result = solver.solve_efsmt_bv([x], [y], fmla)
    duration = time.time() - start
    print(f"Result: {result}")
    print(f"Time: {duration:.3f}s")


if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG)
    test_efsmt()
