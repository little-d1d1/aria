import os
import subprocess
from .literal_mapping import LiteralMapping
from .utils import get_bin_dir, log, print_final_result
from .global_storage import gbl


class CVC5Runner:
    def __init__(self, smt_file):
        self.smt_file = smt_file
        self.cvcoutput = None
        self.mapping = LiteralMapping()

    def run_cvc5_on_smt_file(self):
        log(f"{gbl.time()} Running cvc5 on {self.smt_file}", 1)
        cvc_path = os.path.join(get_bin_dir(), 'cvc5')

        result = subprocess.run([cvc_path, '--boolabs', '-t', 'aiginfo', self.smt_file],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if gbl.verbosity >= 4:
            print(result.stdout)
        if result.returncode != 0:
            if "unsat" in result.stdout:
                log("c cvc5 output indicates UNSAT", 0)
                print_final_result(0)
                exit(0)
            raise RuntimeError(f"cvc5 error: {result.stderr}")
        log(f"cvc5 output: {result.stdout}", 4)
        self.cvcoutput = result.stdout
        log(f"{gbl.time()} Done running cvc5, parsing the output to get atoms", 2)

    def populate_variable_list_in_mapping(self):
        forbidden_atom_starts = ['not', 'let', 'and', 'or']
        log("Parsing cvc5 output to get the variable list", 3)
        pcnfread = False
        if self.cvcoutput is None:
            raise ValueError(
                "cvcoutput is None, ensure run_cvc5_on_smt_file() is called before parsing.")
        for line in self.cvcoutput.splitlines():
            log(f"cvc5 output line: {line}", 5)
            if not line.startswith('c ') or line.startswith('c end') or line.startswith('c AIG'):
                continue
            parts = line.split(':')
            log(f"parts: {parts}", 5)
            if 'skipit' in parts[1]:
                continue
            if any([x in parts[1] for x in forbidden_atom_starts]):
                print(f"WARNING: cvc5 --ttc was not supposed to output {line}")
                # exit(1)

            if "(=" in parts[1]:
                # print("TODO: handle equality constraints")
                continue

            inequality = parts[1].strip()
            literal = int(parts[0][2:])

            log(f"adding variable: {inequality} with literal: {literal}", 5)
            self.mapping.add_variable_in_constraint_matrix(inequality)
        self.mapping.finalize_variable_matrix()

    def parse_cvc5_output(self):
        self.populate_variable_list_in_mapping()
        log("Parsing cvc5 output", 3)
        cnf_lines = []
        pcnfread = False
        # cnffilename replace the last.smth2 with .cnf
        cnf_file_name = self.smt_file.split("/")[-1]
        cnf_file_name = cnf_file_name[:cnf_file_name.rfind('.')] + '.cnf'
        aig_file_name = cnf_file_name[:cnf_file_name.rfind('.')] + '.aag'

        for line in self.cvcoutput.splitlines():  # type: ignore
            if not line.startswith('c') or line.startswith('c end') or line.startswith('c AIG'):
                continue

            parts = line.split(':')
            if 'skipit' in parts[1]:
                continue
            if "(=" in parts[1]:
                # print("TODO: handle equality constraints")
                continue

            literal = int(parts[0][2:])
            inequality = parts[1].strip()
            self.mapping.add_mapping(literal, inequality)
        #

        if gbl.dnfizer == "hall":
            log(f"created AIG file: {aig_file_name}", 3)
            log(
                f"CNF literal to atoms Mapping (b|-A) for Ax<=b: \n{self.mapping}", 4)
        else:
            log(f"created CNF file: {cnf_file_name}")
            log(f"CNF literal to atoms Mapping: \n{self.mapping}", 4)
            aig_file_name = cnf_file_name
            # print("Running HALL")
            # dnf_file = convert_aig_to_dnf(aig_file_name)
            # cubes = parse_dnf_file(dnf_file)
            # print(f"DNF cubes: {cubes}")
        log(f"parsed cvc5 output: {aig_file_name}", 3)
        log(f"{gbl.time()} Done parsing cvc5 output", 2)
        gbl.tempfiles.append(cnf_file_name)
        gbl.tempfiles.append(aig_file_name)

        return self.mapping, aig_file_name
