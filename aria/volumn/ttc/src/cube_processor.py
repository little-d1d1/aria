import pprint
from .latte_runner import run_latte_on_matrix, run_volesti_on_matrix, run_bvcount_on_matrix, run_tool_on_matrix
from .count_by_opt import count_by_optimization_matrix
from .decompose_polytope import decompose_polytope
from .utils import *
import pandas as pd
import sys
from .global_storage import gbl
from .cube_processor_nondis import process_cubes_nondisjoint, process_cubes_bringmann_friedrich
from .polytope_bv import Polytope
from .component_count import process_cubes_componentcount
from .py_benchmark_template import generate_py_benchmark_content

import os

def create_python_file_with_polytopes(cubes, mapping):
    folder_name = "python_polytope"
    if not os.path.exists(folder_name):
        os.makedirs(folder_name)

    py_file_name = os.path.join(folder_name, gbl.filename.split("/")[-1])
    py_file_name = py_file_name[:py_file_name.rfind('.')] + '.py'
    if os.path.exists(py_file_name):
        os.remove(py_file_name)
        log(f"Deleted existing Python file: {py_file_name}", 2)
    log(f"Creating Python file with polytopes: {py_file_name}", 2)

    expr = []
    for cube in cubes:
        terms = []
        polytope = Polytope.create_polytope_from_cube(cube, mapping)
        # polytope is (A, b) format

        for row, rhs in zip(polytope.A, polytope.b):
            # Each row is a list of coefficients for variables
            # Build list of (var_index, coeff) for nonzero coeffs
            terms_row = []
            for idx, coeff in enumerate(row):
                if coeff != 0:
                    terms_row.append((idx, coeff))
                # end if
            rhs = round(rhs, 4)
            terms_row.append(('<=', rhs))
            terms.append(terms_row)

        expr.append(terms)

    dimension = len(mapping.variables)
    monomials = [[1, [0] * dimension]]
    expr_repr = pprint.pformat(expr, width=80)
    mon_repr = pprint.pformat(monomials, width=80)
    content = generate_py_benchmark_content(expr_repr, mon_repr, dimension, 0)


    with open(py_file_name, 'w') as f:
        f.write(content)

    log(f"Created expr: {expr}", 3)

def process_cubes(cubes, mapping):
    if gbl.wmidnf:
        create_python_file_with_polytopes(cubes, mapping)
        exit(0)

    if gbl.count_disjoint_components:
        log(f"{gbl.time()} Processing cubes to count disjoint polytopes", 1)
        return process_cubes_componentcount(cubes, mapping)
    if not gbl.disjoint:
        if gbl.bringmann_friedrich or gbl.abboud:
            algo_name = "Abboud et al." if gbl.abboud else "Bringmann-Friedrich"
            log(f"{gbl.time()} Processing cubes using {algo_name} algorithm", 1)
            return process_cubes_bringmann_friedrich(cubes, mapping, use_abboud=gbl.abboud)
        else:
            return process_cubes_nondisjoint(cubes, mapping)
    log("Processing cubes to get final result", 1)
    final_sum = 0
    result = 0
    ddim_zero = True
    i = 0
    for i, cube in enumerate(cubes):
        log(f"--- {gbl.time()} Processing cube {i+1}/{len(cubes)}", 2)
        log(f"Cube {i+1}: {cube}", 3)
        # matrix_file = "matrix.tmp"
        # latte_file_name = gbl.filename.split("/")[-1]
        # latte_file_name = latte_file_name[:latte_file_name.rfind(
        #     '.')] + '.latte'

        # TODO good file name is not often accepted by latte!!
        # e.g., prime-cone_prime_cone_sat_5
        latte_file_name = f"matrix{i+1}.tmp"
        polytope = Polytope.create_polytope_from_cube(
            cubes[i], mapping, latte_file_name)
        gbl.tempfiles.append(latte_file_name)


        if gbl.decompose_lim > 0:
            latte_filenames = decompose_polytope(
                latte_file_name, gbl.decompose_lim)
            if latte_filenames is not None:
                for latte_file_name in latte_filenames:
                    # run_volesti_on_matrix(latte_file_name)
                    result = run_latte_on_matrix(latte_file_name)
                    final_sum += result
        else:
            if gbl.logic == "lra":
                assert (gbl.logic == "lra")
                if gbl.exactvolume:
                    result = run_tool_on_matrix(
                        latte_file_name, toolname="latteintegrate")
                else:
                    result = run_volesti_on_matrix(latte_file_name)
                if result >= 0:
                    ddim_zero = False
                else:
                    result = 0
            else:
                assert (gbl.logic == "lia")
                if gbl.usebv:
                    result = run_bvcount_on_matrix(latte_file_name, "bv")
                elif gbl.usepact:
                    result = run_bvcount_on_matrix(latte_file_name, "lia")
                elif gbl.useoptcnt:
                    result = count_by_optimization_matrix(latte_file_name)
                else:
                    result = run_latte_on_matrix(latte_file_name)
        log(f"Result from for cube {i+1}: {result}", 2)
        final_sum += result
    if ddim_zero and gbl.logic == "lra" and final_sum == 0:
        log(f"c vol is 0 because of equalities in all {i} cubes", 1)
    return (final_sum)
