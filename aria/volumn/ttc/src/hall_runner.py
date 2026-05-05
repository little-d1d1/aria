import subprocess
import os
import pty
from .utils import get_bin_dir, log
from .global_storage import gbl


def convert_cnf_to_dnf(cnf_file):
    log("Running CNF to DNF converter...", 2)

    cubes_size = 0
    cnftranslate_path = os.path.join(get_bin_dir(), 'cnftranslate')

    dnf_file = cnf_file[:-4] + ".dnf"
    gbl.tempfiles.append(dnf_file)

    command = [cnftranslate_path, cnf_file, dnf_file]

    try:
        result = subprocess.run(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)



        if gbl.verbosity > 3:
            print("Output from cnftranslate:")
            print(result.stdout.decode())
            print("Error from cnftranslate:")
            print(result.stderr.decode())
    except subprocess.CalledProcessError as e:
        raise RuntimeError(
            f"Error occurred while running cnftranslate: {e.stderr.decode()}")
    # if gbl.verbosity >= 2 then print contents of the file dnf_file here
    if gbl.verbosity > 2:
        print(f"Contents of {dnf_file}:")
        with open(dnf_file, 'r') as f:
            print(f.read())

    if gbl.cube_and_exit:
        cubes_size = len(open(dnf_file).readlines()) - 1
        print(f"c Number of cubes: {cubes_size}")
        exit(0)


    return dnf_file


def convert_to_dnf(cnf_file):
    log(f"c Using {gbl.dnfizer} to convert CNF to DNF", 3)
    if gbl.dnfizer == "hall":
        return convert_aig_to_dnf(cnf_file)
    else:
        return convert_cnf_to_dnf(cnf_file)

def convert_aig_to_dnf(aig_file):
    log(f"{gbl.time()} Running AIG to DNF converter...", 1)
    cubes_size = 0
    cnftranslate_path = os.path.join(get_bin_dir(), 'hall_tool')

    dnf_file = aig_file[:-4] + ".dnf"
    gbl.tempfiles.append(dnf_file)

    hall_algo = "roc"
    if gbl.disjoint:
        hall_algo = "mars-dis"

    command = [cnftranslate_path,  aig_file, "/mode",
               hall_algo, "/general/print_enumer", "1"]
    log(f"Running Command: {' '.join(command)}", 3)

    try:
        result = subprocess.run(
            command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,  check=True)
        if gbl.verbosity > 3:
            print("Output from HALL:")
            print(result.stdout.decode())  # type: ignore
            print("Error from HALL:")
            print(result.stderr.decode())  # type: ignore
    except subprocess.CalledProcessError as e:
        raise RuntimeError(
            f"Error occurred while running HALL: {e.stderr.decode()}")
    # if gbl.verbosity >= 2 then print contents of the file dnf_file here
    # put result.stdout.decode() in dnf_file
    with open(dnf_file, 'w') as f:
        # if line starts with c then ignore otherwise write to file
        for lines in result.stdout.decode().splitlines():
            if not lines.startswith('c'):
                f.write(lines + '\n')
                cubes_size += 1

    if gbl.verbosity > 3:
        print(f"Contents of {dnf_file}:")
        with open(dnf_file, 'r') as f:
            print(f.read())

    if gbl.cube_and_exit:
        print(f"c Number of cubes: {cubes_size}")
        exit(0)
    log(f"{gbl.time()} Done running AIG to DNF converter, parsing DNF to get cubes", 1)
    return dnf_file




def parse_dnf_file(dnf_file):
    log("Parsing DNF content", 3)
    cubes = []
    dnf = open(dnf_file, 'r')
    dnf = dnf.read()
    for line in dnf.splitlines():
        if line.strip() and not line.startswith('p'):
            cubes.append([int(lit)
                         for lit in line.strip().split() if lit != '0'])
    log(f"Parsed DNF content: {cubes}", 4)
    log(f"Number of cubes parsed: {len(cubes)}", 1)
    return cubes
