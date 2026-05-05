#!/usr/bin/env python3
"""Template helper to generate Python benchmark files."""


def generate_py_benchmark_content(expr_repr, monomials_repr, cnt_reals, cnt_bools):
    return f'''#!/usr/bin/env python3
import sys
import os

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from simple_wmi_solver import SimpleWMISolver
from utils.reals_universe import RealsUniverse
from utils.weight_function import WeightFunction
import numpy as np
import time


def run_example(eps=0.2, delta=0.1, verbose=False):

    np.random.seed(42)

    cntReals = {cnt_reals}  # Real variables
    cntBools = {cnt_bools}  # Boolean variables

    # Create universe: real variables in [-1000, 1000]
    uni = RealsUniverse(cntReals, lowerBound=-1000, upperBound=1000)

    expr = {expr_repr}
    monomials = {monomials_repr}

    poly_wf = WeightFunction(monomials, np.array([]))

    if not os.path.exists("temp"):
        os.makedirs("temp")

    timestamp_start = time.time()

    task = SimpleWMISolver(expr, cntBools, uni, poly_wf)
    result = task.simpleCoverage(eps, delta)

    timestamp_end = time.time()
    execution_time = timestamp_end - timestamp_start

    return {{
        "result": result,
        "expected": None,
        "execution_time": execution_time,
        "error": None,
        "success": True,
    }}


def main():
    """Command-line interface for the example."""
    result, expected, execution_time, error, success = run_example(verbose=True).values()
    print(f"Result: {{result}}")
    print(f"Expected: {{expected}}")
    print(f"Execution time: {{execution_time:.4f}} seconds")
    if error:
        print(f"Error: {{error}}")
    else:
        print("Success:", success)


if __name__ == "__main__":
    main()
'''
