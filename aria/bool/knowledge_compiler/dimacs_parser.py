"""
DIMACS CNF parsing helpers used by the knowledge compiler.
"""

from __future__ import annotations

import time
from typing import Iterable, List, Tuple


def _parse_lines(lines: Iterable[str], verbose: bool) -> Tuple[List[List[int]], int]:
    initial_time = time.time()
    clauses: List[List[int]] = []
    nvars = 0
    expected_clauses = None
    pending_clause: List[int] = []
    header_seen = False

    if verbose:
        print("=====================[ Problem Statistics ]=====================")
        print("|                                                              |")

    for lineno, raw_line in enumerate(lines, start=1):
        line = raw_line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            tokens = line.split()
            if len(tokens) != 4 or tokens[1] != "cnf":
                raise ValueError(f"Malformed DIMACS header on line {lineno}: {raw_line!r}")
            try:
                nvars = int(tokens[2])
                expected_clauses = int(tokens[3])
            except ValueError as exc:
                raise ValueError(
                    f"Malformed DIMACS counts on line {lineno}: {raw_line!r}"
                ) from exc
            if nvars < 0 or expected_clauses < 0:
                raise ValueError(
                    f"DIMACS header must have non-negative counts on line {lineno}"
                )
            header_seen = True
            if verbose:
                print(f"|   Nb of variables:      {nvars:10d}                           |")
                print(
                    f"|   Nb of clauses:        {expected_clauses:10d}                           |"
                )
            continue

        try:
            literals = [int(token) for token in line.split()]
        except ValueError as exc:
            raise ValueError(f"Malformed literal on line {lineno}: {raw_line!r}") from exc

        for literal in literals:
            if literal == 0:
                clauses.append(pending_clause)
                pending_clause = []
            else:
                pending_clause.append(literal)

    if pending_clause:
        raise ValueError("DIMACS input ended before terminating the last clause with 0")

    if not header_seen:
        inferred_vars = max((abs(lit) for clause in clauses for lit in clause), default=0)
        nvars = inferred_vars

    if expected_clauses is not None and expected_clauses != len(clauses):
        raise ValueError(
            "DIMACS clause count mismatch: header declared {} clauses, parsed {}".format(
                expected_clauses, len(clauses)
            )
        )

    end_time = time.time()
    if verbose:
        print(
            f"|   Parse time:      {end_time - initial_time:10.4f}s"
            f"                               |"
        )
        print("|                                                              |")

    return clauses, nvars


def parse_cnf_string(cnf: str, verbose: bool = False) -> Tuple[List[List[int]], int]:
    """
    Parse a CNF formula from a DIMACS string.
    """

    return _parse_lines(cnf.splitlines(), verbose)


def parse(filename: str, verbose: bool = False) -> Tuple[List[List[int]], int]:
    """
    Parse a CNF formula from a DIMACS file.
    """

    with open(filename, "r", encoding="utf-8") as file:
        return _parse_lines(file, verbose)
