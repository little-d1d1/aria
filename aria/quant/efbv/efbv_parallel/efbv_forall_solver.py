"""Forall Solver for EFBV parallel module."""

import atexit
import logging
import concurrent.futures
import signal
from typing import Dict, List, Optional, Tuple

import z3
from z3.z3util import get_vars
from aria.global_params.paths import global_config
from aria.quant.efbv.efbv_parallel.efbv_utils import FSolverMode
from aria.quant.efbv.efbv_parallel.exceptions import (
    ForAllSolverSuccess,
    ForAllSolverUnknown,
)
from aria.utils.solver.smtlib import SMTLIBSolver

logger = logging.getLogger(__name__)

m_forall_solver_strategy = FSolverMode.PARALLEL_THREAD
_IPC_SOLVER_CACHE: Dict[str, SMTLIBSolver] = {}


def _build_smt2_script(fml: z3.BoolRef) -> str:
    solver = z3.SolverFor("QF_BV")
    solver.add(fml)
    return "(set-logic QF_BV)\n" + solver.to_smt2()


def _get_solver_cmd(solver_name: str) -> str:
    solver_path = global_config.get_solver_path(solver_name)
    if solver_path is None:
        raise ValueError(f"Binary solver not found: {solver_name}")
    if solver_name == "z3":
        return f"{solver_path} -in"
    if solver_name == "cvc5":
        return f"{solver_path} -q -i --produce-models"
    if solver_name == "yices2":
        return f"{solver_path} --incremental"
    return f"{solver_path} -in"


def _sort_spec(sort: z3.SortRef) -> Tuple[str, Optional[int]]:
    if sort.kind() == z3.Z3_BV_SORT:
        return ("bv", sort.size())
    if sort.kind() == z3.Z3_BOOL_SORT:
        return ("bool", None)
    raise ValueError(f"Unsupported sort in efbv process mode: {sort}")


def _make_decl(name: str, sort_kind: str, sort_size: Optional[int], ctx: z3.Context):
    if sort_kind == "bv":
        assert sort_size is not None
        return z3.BitVec(name, sort_size, ctx=ctx)
    if sort_kind == "bool":
        return z3.Bool(name, ctx=ctx)
    raise ValueError(f"Unsupported declaration spec: {(sort_kind, sort_size)}")


def _expr_from_sexpr(
    name: str,
    value_str: str,
    sort_kind: str,
    sort_size: Optional[int],
    ctx: z3.Context,
) -> z3.ExprRef:
    decl = _make_decl(name, sort_kind, sort_size, ctx)
    assertions = z3.parse_smt2_string(
        f"(assert (= {name} {value_str}))",
        decls={name: decl},
        ctx=ctx,
    )
    if not assertions:
        raise ValueError(f"Could not parse value for {name}: {value_str}")
    return assertions[0].arg(1)


def _split_value_pairs(raw: str) -> List[str]:
    s = raw.strip()
    if not s.startswith("(") or not s.endswith(")"):
        return []
    s = s[1:-1].strip()
    pairs = []
    depth = 0
    start = None
    for i, ch in enumerate(s):
        if ch == "(":
            if depth == 0:
                start = i
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and start is not None:
                pairs.append(s[start : i + 1])
                start = None
    return pairs


def _parse_values_output(raw: str) -> Dict[str, str]:
    pairs = _split_value_pairs(raw)
    values: Dict[str, str] = {}
    for pair in pairs:
        body = pair.strip()[1:-1].strip()
        if not body:
            continue
        if body.startswith("|"):
            end_idx = body.find("|", 1)
            if end_idx == -1:
                continue
            name = body[: end_idx + 1].strip()
            value = body[end_idx + 1 :].strip()
        else:
            split_at = body.find(" ")
            if split_at == -1:
                continue
            name = body[:split_at].strip()
            value = body[split_at + 1 :].strip()
        values[name] = value
    return values


def _init_ipc_solver_worker() -> None:
    atexit.register(_shutdown_ipc_solver_worker)
    _register_ipc_cleanup_handlers()


def _shutdown_ipc_solver_worker() -> None:
    for solver in _IPC_SOLVER_CACHE.values():
        solver.stop()
    _IPC_SOLVER_CACHE.clear()


def _handle_ipc_worker_signal(signum: int, _frame) -> None:
    _shutdown_ipc_solver_worker()
    raise SystemExit(128 + signum)


def _register_ipc_cleanup_handlers() -> None:
    for sig_name in ("SIGTERM", "SIGINT", "SIGHUP"):
        sig = getattr(signal, sig_name, None)
        if sig is not None:
            signal.signal(sig, _handle_ipc_worker_signal)


def _terminate_process_pool(
    executor: Optional[concurrent.futures.ProcessPoolExecutor],
) -> None:
    if executor is None:
        return
    processes = getattr(executor, "_processes", None)
    if processes:
        for proc in list(processes.values()):
            try:
                if proc.is_alive():
                    proc.terminate()
            except Exception:
                continue
    executor.shutdown(wait=False, cancel_futures=True)


def _check_in_process(
    task: Tuple[str, List[Tuple[str, str, Optional[int]]], str]
) -> Tuple[str, Optional[List[Tuple[str, str, Optional[int], str]]]]:
    script, var_specs, solver_name = task
    bin_solver = _IPC_SOLVER_CACHE.get(solver_name)
    if bin_solver is None:
        bin_solver = SMTLIBSolver(_get_solver_cmd(solver_name))
        _IPC_SOLVER_CACHE[solver_name] = bin_solver
    bin_solver.reset()
    status = bin_solver.check_sat_from_scratch(script)
    if status.name == "SAT":
        var_names = [name for name, _sort_kind, _sort_size in var_specs]
        raw_values = bin_solver.get_expr_values(var_names) if var_names else ""
        values_map = _parse_values_output(raw_values)
        assignments = []
        for name, sort_kind, sort_size in var_specs:
            value_str = values_map.get(name)
            if value_str is None:
                continue
            assignments.append((name, sort_kind, sort_size, value_str))
        return ("sat", assignments)
    if status.name == "UNSAT":
        return ("unsat", None)
    return ("unknown", None)


class ModelSnapshot:
    """Minimal model wrapper for cross-context variable evaluation."""

    def __init__(self, assignments: Dict[str, z3.ExprRef]):
        self.assignments = assignments

    def eval(self, expr: z3.ExprRef, model_completion: bool = False) -> z3.ExprRef:
        if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            value = self.assignments.get(str(expr))
            if value is not None:
                return value
            if model_completion and z3.is_bv_sort(expr.sort()):
                return z3.BitVecVal(0, expr.size(), ctx=expr.ctx)
        raise KeyError(f"No assignment recorded for expression: {expr}")


class ForAllSolver:
    """Forall solver for EFBV problems."""

    def __init__(
        self,
        ctx: z3.Context,
        forall_vars: Optional[List[z3.ExprRef]] = None,
        num_workers: int = 4,
    ):
        """Initialize forall solver."""
        self.ctx = ctx  # the Z3 context of the main thread
        self.forall_vars = forall_vars or []
        # self.phi = None
        self.num_workers = num_workers
        self.solver_name = "z3"
        self._process_executor: Optional[concurrent.futures.ProcessPoolExecutor] = None

    def push(self):
        """Push solver state (no-op)."""

    def pop(self):
        """Pop solver state (no-op)."""

    def check(self, cnt_list: List[z3.BoolRef]):
        """Check candidate formulas."""
        if m_forall_solver_strategy == FSolverMode.SEQUENTIAL:
            return self.sequential_check(cnt_list)
        if m_forall_solver_strategy == FSolverMode.PARALLEL_THREAD:
            return self.parallel_check_thread(cnt_list)
        if m_forall_solver_strategy == FSolverMode.PARALLEL_PROCESS:
            return self.parallel_check_process(cnt_list)
        raise NotImplementedError

    def sequential_check(self, cnt_list: List[z3.BoolRef]):
        """Check one-by-one."""
        models = []
        solver = z3.SolverFor("QF_BV", ctx=self.ctx)
        for cnt in cnt_list:
            solver.push()
            solver.add(cnt)
            try:
                res = solver.check()
                if res == z3.sat:
                    models.append(solver.model())
                elif res == z3.unsat:
                    raise ForAllSolverSuccess()
                else:
                    raise ForAllSolverUnknown()
            finally:
                solver.pop()
        return models

    def _ensure_worker_pool(self):
        # No longer needed - we create a new solver for each task
        pass

    def _serialize_model(
        self,
        model: z3.ModelRef,
        expr: z3.ExprRef,
        local_forall_vars: List[z3.ExprRef],
    ) -> Dict[str, z3.ExprRef]:
        assignments: Dict[str, z3.ExprRef] = {}
        stack = [expr]
        seen = set()
        while stack:
            current = stack.pop()
            key = current.get_id()
            if key in seen:
                continue
            seen.add(key)
            if z3.is_const(current) and current.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                assignments[str(current)] = model.eval(current, model_completion=True)
            stack.extend(current.children())
        for var in local_forall_vars:
            assignments[str(var)] = model.eval(var, model_completion=True)
        return assignments

    def _check_in_worker(self, worker_idx: int, cnt: z3.BoolRef) -> Dict[str, z3.ExprRef]:
        # Create a new context and solver for each task to avoid thread-safety issues
        # Z3 solvers are not thread-safe, so we cannot reuse solver instances
        del worker_idx
        worker_ctx = z3.Context()
        local_cnt = cnt.translate(worker_ctx)
        local_forall_vars = [var.translate(worker_ctx) for var in self.forall_vars]
        solver = z3.SolverFor("QF_BV", ctx=worker_ctx)
        solver.add(local_cnt)
        res = solver.check()
        if res == z3.sat:
            return self._serialize_model(solver.model(), local_cnt, local_forall_vars)
        if res == z3.unsat:
            raise ForAllSolverSuccess()
        raise ForAllSolverUnknown()

    def parallel_check_thread(self, cnt_list: List[z3.BoolRef]):
        """Solve each formula in cnt_list in parallel."""
        logger.debug("Forall solver: Parallel checking the candidates")
        assignment_sets = []
        task_iter = iter(cnt_list)
        max_in_flight = min(self.num_workers, len(cnt_list))
        executor = concurrent.futures.ThreadPoolExecutor(
            max_workers=self.num_workers
        )
        futures = {}
        early_exit = False
        try:
            for _ in range(max_in_flight):
                cnt = next(task_iter, None)
                if cnt is None:
                    break
                future = executor.submit(self._check_in_worker, 0, cnt)
                futures[future] = cnt

            while futures:
                done, _ = concurrent.futures.wait(
                    futures,
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                for future in done:
                    del futures[future]
                    try:
                        assignment_sets.append(future.result())
                    except (ForAllSolverSuccess, ForAllSolverUnknown):
                        early_exit = True
                        for pending in futures:
                            pending.cancel()
                        futures.clear()
                        raise

                    cnt = next(task_iter, None)
                    if cnt is not None:
                        next_future = executor.submit(self._check_in_worker, 0, cnt)
                        futures[next_future] = cnt
        finally:
            executor.shutdown(wait=not early_exit, cancel_futures=early_exit)
        translated = []
        for assignments in assignment_sets:
            translated.append(
                ModelSnapshot(
                    {
                        name: value.translate(self.ctx)
                        for name, value in assignments.items()
                    }
                )
            )
        return translated

    def parallel_check_process(self, cnt_list: List[z3.BoolRef]):
        """Solve each formula in cnt_list in parallel processes."""
        logger.debug("Forall solver: Parallel checking the candidates with processes")
        if not cnt_list:
            return []
        if self._process_executor is None:
            self._process_executor = concurrent.futures.ProcessPoolExecutor(
                max_workers=self.num_workers,
                initializer=_init_ipc_solver_worker,
            )

        task_specs = []
        for cnt in cnt_list:
            vars_in_cnt = get_vars(cnt)
            var_specs = [
                (str(var), *_sort_spec(var.sort()))
                for var in vars_in_cnt
            ]
            task_specs.append((_build_smt2_script(cnt), var_specs, self.solver_name))

        assignment_sets = []
        task_iter = iter(task_specs)
        max_in_flight = min(self.num_workers, len(task_specs))
        futures = {}
        for _ in range(max_in_flight):
            task = next(task_iter, None)
            if task is None:
                break
            future = self._process_executor.submit(_check_in_process, task)
            futures[future] = task

        while futures:
            done, _ = concurrent.futures.wait(
                futures,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            for future in done:
                del futures[future]
                status, assignments = future.result()
                if status == "sat":
                    assert assignments is not None
                    assignment_sets.append(assignments)
                elif status == "unsat":
                    for pending in futures:
                        pending.cancel()
                    futures.clear()
                    raise ForAllSolverSuccess()
                else:
                    for pending in futures:
                        pending.cancel()
                    futures.clear()
                    raise ForAllSolverUnknown()

                task = next(task_iter, None)
                if task is not None:
                    next_future = self._process_executor.submit(_check_in_process, task)
                    futures[next_future] = task

        translated = []
        for assignments in assignment_sets:
            translated.append(
                ModelSnapshot(
                    {
                        name: _expr_from_sexpr(
                            name,
                            value_str,
                            sort_kind,
                            sort_size,
                            self.ctx,
                        )
                        for name, sort_kind, sort_size, value_str in assignments
                    }
                )
            )
        return translated

    def close(self) -> None:
        if self._process_executor is not None:
            self._process_executor.shutdown(wait=True, cancel_futures=True)
            self._process_executor = None

    def terminate(self) -> None:
        if self._process_executor is not None:
            _terminate_process_pool(self._process_executor)
            self._process_executor = None

    def build_mappings(self):
        """Build the mapping for replacement (not used for now).

        mappings = []
        for v in m:
            mappings.append((z3.BitVec(str(v), v.size(), origin_ctx),
                           z3.BitVecVal(m[v], v.size(), origin_ctx)))
        """
        raise NotImplementedError
