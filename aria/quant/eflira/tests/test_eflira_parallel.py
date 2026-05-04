"""Smoke tests for the EFLIRA parallel solver."""

import concurrent.futures

import pytest
import z3

import aria.quant.eflira.eflira_parallel as eflira_parallel
from aria.quant.eflira.eflira_parallel import (
    EFLIRAResult,
    FSolverMode,
    _parallel_check_candidates_ipc,
    lira_efsmt_with_parallel_cegis,
)


def test_sat_bounded_implication():
    """Bounded forall should be satisfiable."""
    x, y = z3.Ints("x y")
    phi = z3.Implies(z3.And(y >= 0, y <= 5), y - 2 * x < 10)
    res = lira_efsmt_with_parallel_cegis(
        [x],
        [y],
        phi,
        maxloops=6,
        num_samples=2,
        forall_mode=FSolverMode.PARALLEL_THREAD,
        num_workers=3,
    )
    assert res == EFLIRAResult.SAT


def test_sat_trivial_true_sequential():
    """Trivial true constraint should be SAT in sequential mode."""
    x, y = z3.Ints("x y")
    phi = z3.BoolVal(True)
    res = lira_efsmt_with_parallel_cegis(
        [x],
        [y],
        phi,
        maxloops=2,
        num_samples=1,
        forall_mode=FSolverMode.SEQUENTIAL,
        num_workers=1,
    )
    assert res == EFLIRAResult.SAT


def test_unsat_contradiction():
    """forall y. (y < x and y >= x) is unsatisfiable."""
    x, y = z3.Ints("x y")
    phi = z3.And(y < x, y >= x)
    res = lira_efsmt_with_parallel_cegis(
        [x],
        [y],
        phi,
        maxloops=2,
        num_samples=1,
        forall_mode=FSolverMode.SEQUENTIAL,
        num_workers=1,
    )
    assert res == EFLIRAResult.UNSAT


def test_ipc_parallel_check_stops_submitting_after_terminal_result(monkeypatch):
    """Do not submit more IPC work once a completed task returns UNSAT."""

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
                future = FakeFuture(("UNSAT", ""))
            else:
                future = FakeFuture(("SAT", ""))
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
        eflira_parallel.concurrent.futures,
        "ProcessPoolExecutor",
        fake_pool_factory,
    )
    monkeypatch.setattr(eflira_parallel.concurrent.futures, "wait", fake_wait)

    x = z3.Int("x")
    results = _parallel_check_candidates_ipc(
        [x > 0, x > 1, x > 2],
        var_names=[],
        logic="QF_LIA",
        solver_name="z3",
        num_workers=1,
    )
    assert results == [("UNSAT", "")]
    assert len(fake_executor.submitted) == 1
    assert fake_executor.shutdown_calls == [(True, True)]


def test_ipc_worker_signal_handler_closes_cached_solvers(monkeypatch):
    """Worker signal handler should close cached SMTLIB solvers before exit."""

    class FakeSolver:
        def __init__(self):
            self.stopped = False

        def stop(self):
            self.stopped = True

    fake_solver = FakeSolver()
    monkeypatch.setattr(
        eflira_parallel,
        "_IPC_SOLVER_CACHE",
        {"z3": fake_solver},
    )

    with pytest.raises(SystemExit) as excinfo:
        eflira_parallel._handle_ipc_worker_signal(15, None)

    assert excinfo.value.code == 143
    assert fake_solver.stopped is True
    assert eflira_parallel._IPC_SOLVER_CACHE == {}


def test_parent_pool_cleanup_handler_closes_solver():
    """Parent signal handler should close the active solver pool before exit."""
    closed = []

    handler = eflira_parallel._make_parent_cleanup_handler(
        lambda: closed.append("closed")
    )

    with pytest.raises(SystemExit) as excinfo:
        handler(15, None)

    assert excinfo.value.code == 143
    assert closed == ["closed"]
