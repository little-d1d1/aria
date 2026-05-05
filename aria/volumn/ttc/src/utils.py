import os
import subprocess
import argparse
from .global_storage import gbl
import numpy as np
import random
import string
import pandas as pd
import time
import math


def get_arg_parser():
    parser = argparse.ArgumentParser(
        description="This is the TTC, Toolbox for Theory Counting.")
    parser.add_argument('smt_file', type=str,
                        help='Path to the SMT-LIB 2 file.')
    parser.add_argument('-v', '--verbosity', type=int,
                        default=0, help='Set verbosity level.')
    parser.add_argument("-d", "--disjoint", action="store_true",
                        help='Use disjoint decomposition in LRA (disjoint is defualt in LIA).')
    parser.add_argument("-e", "--exactvol", action="store_true",
                        help='Use exact volume computation for polytopes with LattE.')
    parser.add_argument("--nohall", action="store_true",
                        help='Use the Karnaugh map extension to convert CNF to DNF, default is HALL tool.')
    parser.add_argument("--cubes", action="store_true",
                        help='Decompose into cubes and exit.')
    parser.add_argument("--intbv", action="store_true", default=False,
                        help='Count lattice points using bv counter.')
    parser.add_argument("--pact", action="store_true", default=False,
                        help='Count lattice points using pact counter.')
    parser.add_argument("--optcnt", action="store_true", default=False,
                        help='Count lattice points by solving optimization.')
    parser.add_argument("-l", "--decomposelim", type=int, default=0,
                        help='Limit on the number of decompositions.')
    parser.add_argument("--seed", type=int, default=123,
                        help='Random seed to use in random algorithms.')
    parser.add_argument("--dontdelete", action="store_true",
                        help='Do not delete temporary files.')
    parser.add_argument("--eps", type=float, default=0.8,
                        help='Epsilon value for the approximation algorithm.')
    parser.add_argument("--delta", type=float, default=0.2,
                        help='Delta value for the approximation algorithm.')
    parser.add_argument("--volepsfrac", type=float, default=0.5,
                        help='Epsilon value multiplier for the volume approximation algorithm.')
    parser.add_argument("-c", "--countdisjoint", action="store_true",
                        help='Count disjoint components in the solution space.')
    parser.add_argument("-g", "--volguarantee", action="store_true",
                        help='Use guaranteed algorithm for the approximation algorithm.')
    parser.add_argument("--wmidnf", action="store_true",
                        help='Create a Python file with polytopes for the WMI-DNF tool.')
    parser.add_argument("-bf", "--bringmannfriedrich", action="store_true",
                        help='Use Bringmann-Friedrich algorithm for union of polytopes in LRA.')
    parser.add_argument("--abboud", action="store_true",
                        help='Use Abboud et al. algorithm for union of polytopes in LRA.')


    return parser





def get_bin_dir():
    """Resolve the directory holding native helper binaries (cvc5, lrs, ...).

    Prefers TTC_BIN_DIR (set by the pipx bootstrap to its state dir). Falls
    back to <repo>/bin for dev checkouts and the install.sh tarball layout.
    """
    bin_dir = os.environ.get("TTC_BIN_DIR")
    if bin_dir:
        return bin_dir
    script_dir = os.path.dirname(os.path.abspath(__file__))
    parent_dir = os.path.dirname(script_dir)
    return os.path.join(parent_dir, 'bin')


def check_existence_of_tools(tools):
    bin_dir = get_bin_dir()
    log(f"bin_dir: {bin_dir}", 4)
    for tool in tools:
        tool_path = os.path.join(bin_dir, tool)
        if not os.path.isfile(tool_path):
            raise EnvironmentError(f"{tool} not found in the 'bin' directory.")
        if not os.access(tool_path, os.X_OK):
            raise EnvironmentError(
                f"{tool} is not executable in the 'bin' directory.")

def write_matrix_to_file(matrix, output_file):
    log(f"Writing matrix to file: {output_file}", 4)
    matrix_array = matrix.to_numpy()
    if gbl.exactvolume:
        # Convert to integer representation
        if np.all(matrix_array % 1 == 0):
            matrix_array = matrix_array.astype(int)
        else:
            matrix_array = matrix_array* 1000000
            matrix_array = matrix_array.astype(int)

    # Get the size of the matrix
    num_constraints, num_variables = matrix_array.shape

    with open(output_file, 'w') as f:
        f.write(f"{num_constraints} {num_variables}\n")
        for row in matrix_array:
            f.write(" ".join(map(str, row)) + "\n")


def get_git_commit_id():
    try:
        # Run the command and decode the byte output to a string
        commit_id = subprocess.check_output(
            ["git", "rev-parse", "HEAD"]).strip().decode('utf-8')
    except subprocess.CalledProcessError:
        commit_id = "unknown"
    return commit_id[:10]


def print_banner(args):
    log("c TTC - Toolbox for Theory Counting", 1)
    # log(f"c Git Version: {get_git_commit_id()}", 1)
    statem  = " ".join(args)
    log(f"c Run with command {statem}", 1)
    if gbl.logic == "lra":
        logic = "QF_LRA"
    elif gbl.logic == "lia":
        logic = "QF_LIA"
    print(f"c Logic set to: {logic}")


def print_final_result(final_result):
    log(f"Total time: {(time.time() - gbl.starttime):.3f} s")

    if final_result > 0:
        logval = math.log10(final_result)
        print(f"c s log10-estimate {logval:.3f}")

    if gbl.logic == "lia":
        resultstr = "s mc"
    elif gbl.logic == "lra" and gbl.count_disjoint_components:
        resultstr = "s disjoint-components"
    else:
        resultstr = "s vol"
    print(f"{resultstr} {final_result}")

def log(message, level=1):
    if gbl.verbosity >= level:
        print(message)


def clean_on_exit(temp_files):
    log("Cleaning up...", 2)
    for file in temp_files:
        if os.path.exists(file):
            os.remove(file)
            log(f"Removed {file}", 3)
    log("Cleaned up.", 2)


def create_all_polytope_files(cubes, mapping):
    filenames = []
    random_prefix = ''.join(random.choice(string.ascii_letters)
                            for _ in range(8))
    for i, cube in enumerate(cubes):
        filename = create_polytope_from_cube(
            cube, mapping, f"{random_prefix}_cube{i+1}.ine")
        filenames.append(filename)
    log(f"Created {len(filenames)} polytope files", 2)
    return filenames

def cleanup():
    if gbl.dontdelete:
        log("Skipping cleanup as --dontdelete is set", 3)
        return
    files = gbl.tempfiles
    log("Cleaning up...", 3)
    for file in files:
        if os.path.exists(file):
            os.remove(file)
            log(f"Removed {file}", 4)
    log("Cleaned up.", 3)


