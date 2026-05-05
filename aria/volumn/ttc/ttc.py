#!/usr/bin/env python3
import os
import sys

from _bootstrap import ensure_ready

_bin_dir = ensure_ready()
os.environ["TTC_BIN_DIR"] = str(_bin_dir)
os.environ["PATH"] = str(_bin_dir) + os.pathsep + os.environ.get("PATH", "")

from src import *


def ttc():

    parser = get_arg_parser()
    args = parser.parse_args()

    gbl.initialize(args)
    print_banner(sys.argv)

    check_existence_of_tools(gbl.tool_list)

    cvcrunner = CVC5Runner(args.smt_file)

    cvcrunner.run_cvc5_on_smt_file()
    mapping, cnf_file = cvcrunner.parse_cvc5_output()

    dnf_file = convert_to_dnf(cnf_file)
    cubes = parse_dnf_file(dnf_file)

    final_result = process_cubes(cubes, mapping)
    print_final_result(final_result)

    cleanup()


if __name__ == "__main__":
    ttc()
