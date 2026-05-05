import math
import fractions
import subprocess
import os
import re
import sys
from .utils import get_bin_dir, log
import threading
from .global_storage import gbl
from .polytope_bv import Polytope
from .polytope_operations import canonicalize
import pandas as pd




def stream_output(pipe, output_list):
    for line in iter(pipe.readline, ''):
        if gbl.verbosity >= 4:
            sys.stdout.write(f"{line}")
            sys.stdout.flush()
        output_list.append(line)
    pipe.close()


def run_tool_on_matrix(matrix_file, toolname, timeout=3600):
    log(f"Running {toolname}...", 3)
    count_command = get_count_command(toolname)
    if isinstance(count_command, list):
        if toolname == "latteintegrate":
            count_command.append(matrix_file)
        else:
            count_command.insert(1, matrix_file)
    else:
        count_command = [count_command, matrix_file]
    log(f"{toolname} command:  {count_command}", 3)

    stdout_lines = []
    stderr_lines = []



    try:
        with subprocess.Popen(count_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1, universal_newlines=True) as proc:
            stdout_thread = threading.Thread(
                target=stream_output, args=(proc.stdout, stdout_lines))
            stderr_thread = threading.Thread(
                target=stream_output, args=(proc.stderr, stderr_lines))

            stdout_thread.start()
            stderr_thread.start()

            try:
                proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                proc.kill()
                stdout_thread.join()
                stderr_thread.join()
                raise RuntimeError(
                    f"{toolname} process timed out after 1 hour")

            stdout_thread.join()
            stderr_thread.join()

            # Join the captured output
            stdout = ''.join(stdout_lines)
            stderr = ''.join(stderr_lines)

            if proc.returncode != 0:
                raise RuntimeError(
                    f"{toolname} exited with return code {proc.returncode}\n"
                    f"stdout:\n{stdout.strip() or '<empty>'}\n"
                    f"stderr:\n{stderr.strip() or '<empty>'}"
                )

            # Check for specific error message in stdout or stderr
            count = handle_output(stdout, stderr, toolname)

            if gbl.logic == "lia":
                count = int(count)
            else:
                count = float(count)

            return count

    except subprocess.CalledProcessError as e:
        print(f"An error occurred: {e}", file=sys.stderr)
        sys.exit(1)


def get_count_command(toolname):
    if toolname == "latte":
        latte_path = os.path.expanduser("~/latte/bin/count")
        if not os.path.isfile(latte_path):
            raise FileNotFoundError(
                f"{latte_path} does not exist. Please ensure that the tool is installed correctly.")
        return latte_path
    elif toolname.startswith("volesti"):
        volesti_path = os.path.join(get_bin_dir(), 'volume')
        if not os.path.isfile(volesti_path):
            raise FileNotFoundError(
                f"{volesti_path} does not exist. Please ensure that the tool is installed correctly.")
        volesti_command = [volesti_path, "--seed",
                           str(gbl.seed), "--epsilon", str(gbl.voleps)]
        if gbl.volesti_guaranteed:
            volesti_command.append("--walklen")
            volesti_command.append(str(gbl.volesti_walk_length))
        # TODO: make this correct
        if "vp" in toolname:
            volesti_command.append("--vpoly")
        return volesti_command
    elif toolname == "latteintegrate":
        latte_path = os.path.expanduser("~/latte/bin/integrate")
        if not os.path.isfile(latte_path):
            raise FileNotFoundError(
                f"{latte_path} does not exist. Please ensure that the tool is installed correctly.")
        latte_path = [latte_path, "--valuation=volume"]
        return latte_path

    else:
        raise ValueError(f"Unknown toolname: {toolname}")


def handle_output(stdout_, stderr_, toolname):
    error_message = "is unbounded"
    count = -1.0
    empty_polytope_message = "Empty polytope or unbounded polytope!"
    if error_message in stdout_ or error_message in stderr_:
        log(
            "Unbounded polytope!\n TODO: Make sure this polytope is not empty", 0)
        sys.exit(0)
    if (empty_polytope_message in stdout_ or empty_polytope_message in stderr_):
        log("Empty polytope!", 3)
    elif toolname == "latte":
        with open("numOfLatticePoints", 'r') as f:
            count = f.read()
    elif toolname.startswith("volesti"):
        for line in stdout_.splitlines():
            if line.startswith("c vol") or line.startswith("s vol"):
                parts = line.split()
                if parts[2] == "inf":
                    return 0
                count = float(parts[2])
                if count < 0:
                    print(f"c WARNING: Volume is negative ({count})")
                break
        if count == -1:
            raise ValueError(
                f"Volume line not found in {toolname} output.\n"
                f"stdout:\n{stdout_.strip() or '<empty>'}\n"
                f"stderr:\n{stderr_.strip() or '<empty>'}"
            )
    elif toolname == "latteintegrate":
        for line in stdout_.splitlines():
            if line.startswith("     Decimal"):
                parts = line.split()
                count = float(parts[1])
                if count < 0:
                    print(f"c WARNING: Volume is negative ({count})")
                break
        if count == -1:
            raise ValueError(
                "Volume line not found in latteintegrate output.\n"
                f"stdout:\n{stdout_.strip() or '<empty>'}\n"
                f"stderr:\n{stderr_.strip() or '<empty>'}"
            )
    else:
        raise ValueError(f"Unknown toolname: {toolname}")

    return count


def run_latte_on_matrix(matrix_file, timeout=3600):
    toolname = "latte"
    return run_tool_on_matrix(matrix_file, toolname, timeout)


def convert_fraction_to_decimal(input_file_path, output_file_path):
    """
    Reads each line from input_file_path, ignores any line starting with '*',
    and replaces fractional values (e.g., 119/86) with their decimal
    representation. Writes all processed lines to output_file_path.

    Example lines:
        1  119/86 -54/43 -39/43
    become, for instance:
        1  1.3837 -1.2558 -0.90698
    (printed with Python's default float precision; actual decimals may differ
    slightly depending on the fraction.)

    The rest of the formatting (line beginnings, number of spaces before/after
    tokens, etc.) is preserved as closely as possible. Any line starting with '*'
    is completely ignored in the output.
    """

    fraction_pattern = re.compile(r'([-+]?\d+(?:\.\d+)?)/(\d+(?:\.\d+)?)')

    with open(input_file_path, 'r') as fin, open(output_file_path, 'w') as fout:
        for line in fin:
            # Ignore comment lines that start with '*'
            if line.lstrip().startswith('*'):
                continue

            # Function to replace "num/den" with a decimal
            def replace_fraction(match):
                # match.group(1) is the numerator part, match.group(2) is denominator
                numerator = fractions.Fraction(match.group(1))
                denominator = fractions.Fraction(match.group(2))
                val = numerator / denominator
                # Convert fraction to float, then to string
                return str(float(val))

            # Replace all fractional tokens with decimals
            # This preserves the original line's spacing around tokens,
            # but the fractional token itself is replaced in-place.
            new_line = fraction_pattern.sub(replace_fraction, line)

            fout.write(new_line)

def latte_to_ine_nofraction(input_file_path, output_file_path):
    with open(input_file_path, 'r') as f_in, open(output_file_path, 'w') as f_out:
        lines = f_in.readlines()
        # First line has two integers: number of constraints (m) and dimension (n)
        m, n = map(int, lines[0].strip().split())
        constraints = [line.strip() for line in lines[1:] if line.strip()]

        # Write to .ine file
        f_out.write("H-representation\n")
        f_out.write("begin\n")
        f_out.write(f" {m} {n} rational\n")
        for line in constraints:
            f_out.write(f" {line}\n")
        f_out.write("end\n")
        log(f"Converted {input_file_path} to {output_file_path}", 3)
        return 0


def latte_to_ine(input_file_path, output_file_path):
    with open(input_file_path, 'r') as f_in, open(output_file_path, 'w') as f_out:
        lines = f_in.readlines()
        # First line has two integers: number of constraints (m) and dimension (n)
        m, n = map(int, lines[0].strip().split())
        constraints = [line.strip() for line in lines[1:] if line.strip()]

        # Write the header to the .ine file
        f_out.write("H-representation\n")
        f_out.write("begin\n")
        f_out.write(f" {m} {n} rational\n")

        # Process each line: rationalize coefficients so they become integers
        for line in constraints:
            parts = line.split()
            # Convert each part to a Fraction
            frac_parts = [fractions.Fraction(p) for p in parts]

            # Compute LCM of denominators
            lcm_denom = 1
            for frac_part in frac_parts:
                lcm_denom = (
                    lcm_denom * frac_part.denominator) // math.gcd(lcm_denom, frac_part.denominator)

            # Multiply each fraction by the LCM to get integer coefficients
            int_parts = [frac_part * lcm_denom for frac_part in frac_parts]

            # Write out the integerized line
            f_out.write(" " + " ".join(str(int(p)) for p in int_parts) + "\n")

        f_out.write("end\n")

def convert_latte_to_polytope(matrix_file, type="vpolytope"):
    use_latte2ine_bin = False
    log(f"Converting latte to vpolytope...", 1)
    bin_dir = get_bin_dir()
    latte2ine_path = os.path.join(bin_dir, 'latte2ine')
    lrs_path = os.path.join(bin_dir, 'lrs')

    if not os.path.isfile(latte2ine_path) and use_latte2ine_bin:
        raise FileNotFoundError(
            f"{latte2ine_path} does not exist. Please ensure that the tool is installed correctly.")
    if not os.path.isfile(lrs_path):
        raise FileNotFoundError(
            f"{lrs_path} does not exist. Please ensure that the tool is installed correctly.")

    ine_file = matrix_file + ".ine"

    if use_latte2ine_bin:
        with open(matrix_file, 'r') as infile, open(ine_file, 'w') as outfile:
            result = subprocess.run([latte2ine_path], text=True,
                                    stdin=infile, stdout=outfile, stderr=subprocess.PIPE)
    else:
        result = latte_to_ine(matrix_file, ine_file)

    if type == "hpolytope":
        return ine_file
    else:
        assert(type == "vpolytope")

    ext_file_temp = matrix_file + ".ext_temp"
    ext_file = matrix_file + ".ext"
    result = subprocess.run([lrs_path, ine_file, ext_file_temp],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    convert_fraction_to_decimal(ext_file_temp, ext_file)
    if result.returncode != 0:
        raise RuntimeError(
            f"latte2vpolytope failed with return code {result.returncode}")
    return ext_file


def run_volesti_on_matrix(matrix_file, epsilon = 0.2,  timeout=3600):
    use_vpolytope = False
    gbl.voleps = epsilon
    if use_vpolytope:
        ext_file = convert_latte_to_polytope(matrix_file, type="vpolytope")
        with open(ext_file, 'r') as f:
            x = f.read()
            if "No feasible solution" in x:
                log("c [ttc->transformtovpolytope] No feasible solution found in this matrix", 4)
                return 0
        volume = run_tool_on_matrix(ext_file, toolname="volesti_vp")
    else:
        # ine_file = convert_latte_to_polytope(matrix_file, type="hpolytope")
        canonicalized_ine = canonicalize(matrix_file)
        if canonicalized_ine == -1:
            volume = -1
        else:
            volume = run_tool_on_matrix(canonicalized_ine, toolname="volesti")
    return volume



def run_bvcount_on_matrix(matrix_file, encoding = "bv", timeout=3600):
    polytope = Polytope.from_file(matrix_file)
    count = polytope.count_lattice_points_smt(encoding)
    return count


def run_volesti_sampling_on_matrix(matrix_file, n, timeout=3600):
    if n <= 0:
        log(f"c [ttc->sampling] asked to sample no points", 2)
        df = pd.DataFrame()
        return df
    elif n > 1:
        log(f"{gbl.time()} Generating {n} points", 2)
    canonicalized_ine = canonicalize(matrix_file)
    volesti_path = os.path.join(get_bin_dir(), 'sample')
    if not os.path.isfile(volesti_path):
        raise FileNotFoundError(
            f"{volesti_path} does not exist. Please ensure that the tool is installed correctly.")
    samples_file = matrix_file + ".samples"
    sample_command = [volesti_path,
                       canonicalized_ine, samples_file, "-n", str(n), "--seed", str(gbl.seed)]

    samples_found = False
    df = None
    attempts = 0
    base_command = sample_command


    while not samples_found:

        stdout_lines = []
        stderr_lines = []
        attempts += 1

        try:
            with subprocess.Popen(sample_command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1, universal_newlines=True) as proc:
                stdout_thread = threading.Thread(
                    target=stream_output, args=(proc.stdout, stdout_lines))
                stderr_thread = threading.Thread(
                    target=stream_output, args=(proc.stderr, stderr_lines))

                stdout_thread.start()
                stderr_thread.start()
                proc.wait(timeout=timeout)
                stdout_thread.join()
                stderr_thread.join()

                # Join the captured output
                stdout = ''.join(stdout_lines)
                stderr = ''.join(stderr_lines)


        except subprocess.CalledProcessError as e:
            print(f"An error occurred: {e}", file=sys.stderr)
            sys.exit(1)

        if os.path.exists(samples_file) and os.path.getsize(samples_file) > 0:
            samples_found = True
            df = pd.read_csv(samples_file, sep=r'\s+', header=None)
            log(f"Sampled {df.shape[0]} points, dimensions {df.shape[1]}", 3)
            df = df.to_numpy()
            if df.shape[0] < int(n) or pd.isna(df[0][0]):
                log(f"Samples file is not correct. got {df.shape[0]}/{n} samples, first value {df[0][0]}/{pd.isna(df[0][0])} Retrying...", 2)
                if (attempts == 1):
                    sample_command = base_command + ["--algorithm", "accelarated"]
                elif (attempts == 2):
                    sample_command = base_command + ["--algorithm", "gaussian"]
                else:
                    log("All sampling attempts failed, no points to return!!!", 2)
                    return df
                samples_found = False

        else:
            if (attempts == 1):
                sample_command = base_command + ["--algorithm", "accelarated"]
            elif (attempts == 2):
                sample_command = base_command + ["--algorithm", "gaussian"]
            else:
                log("All sampling attempts failed, no points to return!!!", 2)
                return df
            log("Samples file is empty. Retrying...", 2)

    gbl.tempfiles.append(samples_file)
    return df








def get_polytope_from_cube(cube, mapping):
    dfd = pd.DataFrame(columns=mapping.constraint_matrix.columns)
    for literal in cube:
        if literal in [0, 1, -2]:
            continue
        # if lit is not in constraint_matrix, then show warning and exit
        if literal not in mapping.constraint_matrix.index:
            log(f"Literal {literal} not found in constraint matrix", 3)
            continue
        temp_row = mapping.constraint_matrix.loc[[literal]]
        dfd = pd.concat([dfd, temp_row])
    # After processing all literals, convert dfd into the matrix form Ax <= b.
    # Assumes that the last column of dfd represents the constant terms.
    if not dfd.empty:
        A = dfd.iloc[:, :-1].to_numpy()
        b = dfd.iloc[:, -1].to_numpy()
        return Polytope(A, b)
    else:
        return Polytope(np.array([]), np.array([]))
