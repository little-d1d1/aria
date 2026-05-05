import time
import os

def check_existence_of_smt_file(smt_file):
    if not os.path.exists(smt_file):
        raise FileNotFoundError(f"c Input file not found in {smt_file}")

class GlobalStorage:
    cnf_file = ""
    dnf_file = ""
    filename = ""
    matrix_file = ""
    verbosity = 0
    decompose_lim = 0
    dimension = 0
    # tool_list = ['cvc5', 'hall', 'latte']
    tool_list = ['cvc5']
    dnfizer = "hall"
    cube_and_exit = False
    count_disjoint_components = False
    arg = None
    logic = ""
    epsilon = 0.8
    delta = 0.2
    volepsfrac = 0.5

    # options
    usebv = False
    usepact = False
    useoptcnt = False
    volesti_algo = "coolinggauss"
    volesti_algo = "coolingball"
    disjoint = False
    bringmann_friedrich = False
    abboud = False
    # volesti_algo = "--seqball"
    volesti_walk_length = 2147483647
    volesti_guaranteed = False
    starttime = 0
    tempfiles = ["tri.ead", "tri.iad", "tri.ecd",
                 "tri.icd", "tri.ine", "tri.ext",
                 "Check_emp.lps", "Check_emp.out",
                 "Check_emp.lp", "numOfLatticePoints"]
    exactvolume = False

    time_volumecomp = 0
    time_decompose = 0
    time_cvc5 = 0
    time_pepin = 0
    seed = 123
    dontdelete = False
    voleps = 0.2
    wmidnf = False

    def set_logic(self):
        with open(self.filename, 'r') as file:
            for line in file:
                if line.startswith("(set-logic"):
                    if "QF_LRA" in line:
                        self.logic = "lra"
                    elif "QF_LIA" in line:
                        self.logic = "lia"
                    else:
                        print(f"logic {line.strip()} is not supported yet")
                        exit(1)
                    break

    # defining the class constructor
    def initialize(self, _arg):
        check_existence_of_smt_file(_arg.smt_file)
        self.arg = _arg
        self.verbosity = _arg.verbosity
        self.filename = _arg.smt_file
        self.set_logic()
        if _arg.nohall:
            self.dnfizer = "cnftranslate"
            self.tool_list.append('cnftranslate')
        else:
            self.tool_list.append('hall_tool')
        self.decompose_lim = _arg.decomposelim
        self.cube_and_exit = _arg.cubes
        self.usebv = _arg.intbv
        self.usepact = _arg.pact
        self.useoptcnt = _arg.optcnt
        self.volepsfrac = _arg.volepsfrac
        self.volesti_guaranteed = _arg.volguarantee
        self.bringmann_friedrich = _arg.bringmannfriedrich
        self.abboud = _arg.abboud
        if self.logic == "lra":
            self.disjoint = _arg.disjoint
        else:
            self.disjoint = False
        self.starttime = time.time()
        self.seed = _arg.seed
        self.dontdelete = _arg.dontdelete
        self.exactvolume = _arg.exactvol
        self.epsilon = _arg.eps
        self.delta = _arg.delta
        self.count_disjoint_components = _arg.countdisjoint
        self.wmidnf = _arg.wmidnf

    def time(self):
        return f"[{(time.time() - self.starttime):.3f} s]"


gbl = GlobalStorage()
