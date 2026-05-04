"""Smoke tests for the EFBV parallel solver."""

import concurrent.futures
import random

import pytest
import z3

pytest.importorskip("pysat.formula")

from aria.quant.efbv.efbv_parallel import efbv_forall_solver
import aria.quant.efbv.efbv_parallel.efbv_cegis_parallel as efbv_cegis_parallel
from aria.quant.efbv.efbv_parallel.efbv_cegis_parallel import (
    EFBVResult,
    ParallelEFBVSolver,
    bv_efsmt_with_uniform_sampling,
)
from aria.quant.efbv.efbv_parallel.exceptions import ForAllSolverSuccess
from aria.quant.efbv.efbv_parallel.efbv_utils import FSolverMode


def setup_module():
    random.seed(0)


def test_sat_trivial_formula():
    """Tautology should be reported SAT."""
    x, y = z3.BitVecs("x y", 2)
    phi = z3.Or(y == x, y != x)  # always true
    res = bv_efsmt_with_uniform_sampling(
        [x],
        [y],
        phi,
        maxloops=4,
        num_samples=2,
    )
    assert res == EFBVResult.SAT


def test_unsat_all_y_equal_x():
    """No single x can equal every y."""
    x, y = z3.BitVecs("x y", 2)
    phi = y == x
    res = bv_efsmt_with_uniform_sampling(
        [x],
        [y],
        phi,
        maxloops=6,
        num_samples=2,
    )
    assert res == EFBVResult.UNSAT


def test_unsat_guarded_parallel_forall():
    """Exercise parallel forall mode on a guarded contradiction."""
    efbv_forall_solver.m_forall_solver_strategy = FSolverMode.PARALLEL_THREAD
    x, y = z3.BitVecs("x y", 4)
    phi = z3.Implies(y > 2, y < x)
    res = bv_efsmt_with_uniform_sampling(
        [x],
        [y],
        phi,
        maxloops=4,
        num_samples=2,
    )
    assert res == EFBVResult.UNSAT


def test_parallel_forall_stops_submitting_after_terminal_result():
    """Do not submit more work once a completed task already proves SAT."""
    solver = efbv_forall_solver.ForAllSolver(z3.Context(), num_workers=1)
    started = []

    def fake_check_in_worker(worker_idx, cnt):
        del worker_idx, cnt
        started.append(len(started))
        raise ForAllSolverSuccess()

    solver._check_in_worker = fake_check_in_worker  # type: ignore[method-assign]
    with pytest.raises(ForAllSolverSuccess):
        solver.parallel_check_thread(
            [z3.BoolVal(True), z3.BoolVal(True), z3.BoolVal(True)]
        )
    assert started == [0]


def test_parallel_process_forall_stops_submitting_after_terminal_result(monkeypatch):
    """Do not submit more process work once a completed task already proves SAT."""

    class FakeFuture:
        def __init__(self, result):
            self._result = result

        def result(self):
            return self._result

        def cancel(self):
            return True

    class FakeExecutor:
        def __init__(self, max_workers):
            self.max_workers = max_workers
            self.submitted = []
            self.shutdown_calls = []

        def submit(self, fn, task):
            del fn
            idx = len(self.submitted)
            if idx == 0:
                future = FakeFuture(("unsat", None))
            else:
                future = FakeFuture(("sat", [("x", "#b0")]))
            self.submitted.append(task)
            return future

        def shutdown(self, wait=True, cancel_futures=False):
            self.shutdown_calls.append((wait, cancel_futures))

    fake_executor = FakeExecutor(max_workers=1)

    def fake_pool_factory(max_workers, initializer=None):
        assert max_workers == 1
        del initializer
        return fake_executor

    def fake_wait(futures, return_when):
        assert return_when == concurrent.futures.FIRST_COMPLETED
        future = next(iter(futures))
        return {future}, set()

    monkeypatch.setattr(
        efbv_forall_solver.concurrent.futures,
        "ProcessPoolExecutor",
        fake_pool_factory,
    )
    monkeypatch.setattr(efbv_forall_solver.concurrent.futures, "wait", fake_wait)

    solver = efbv_forall_solver.ForAllSolver(z3.Context(), num_workers=1)
    with pytest.raises(ForAllSolverSuccess):
        solver.parallel_check_process(
            [z3.BoolVal(True), z3.BoolVal(True), z3.BoolVal(True)]
        )
    assert len(fake_executor.submitted) == 1
    solver.close()
    assert fake_executor.shutdown_calls == [(True, True)]


def test_parallel_efbv_defaults_num_samples_to_num_workers():
    """Default sampling count should track worker count."""
    solver = ParallelEFBVSolver(num_workers=8)
    assert solver.num_samples == 8


def test_parallel_process_worker_signal_handler_closes_cached_solvers(monkeypatch):
    """Worker signal handler should close cached SMTLIB solvers before exit."""

    class FakeSolver:
        def __init__(self):
            self.stopped = False

        def stop(self):
            self.stopped = True

    fake_solver = FakeSolver()
    monkeypatch.setattr(
        efbv_forall_solver,
        "_IPC_SOLVER_CACHE",
        {"z3": fake_solver},
    )

    with pytest.raises(SystemExit) as excinfo:
        efbv_forall_solver._handle_ipc_worker_signal(15, None)

    assert excinfo.value.code == 143
    assert fake_solver.stopped is True
    assert efbv_forall_solver._IPC_SOLVER_CACHE == {}


def test_parent_pool_cleanup_handler_closes_solver():
    """Parent signal handler should close the active solver pool before exit."""
    closed = []

    handler = efbv_cegis_parallel._make_parent_cleanup_handler(
        lambda: closed.append("closed")
    )

    with pytest.raises(SystemExit) as excinfo:
        handler(15, None)

    assert excinfo.value.code == 143
    assert closed == ["closed"]


@pytest.mark.xfail(reason="Sampler sometimes misses satisfying candidates; investigate EFBV exists sampling.")
def test_sat_exists_solution_found():
    """Ensure a concrete candidate is validated (currently flaky/unsupported)."""
    efbv_forall_solver.m_forall_solver_strategy = FSolverMode.SEQUENTIAL
    x, y = z3.BitVecs("x y", 3)
    phi = z3.Implies(z3.And(y >= 0, y <= 3), y + x >= 1)
    res = bv_efsmt_with_uniform_sampling(
        [x],
        [y],
        phi,
        maxloops=8,
        num_samples=4,
    )
    assert res == EFBVResult.SAT
