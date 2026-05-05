import argparse
import z3
import os
import random
import multiprocessing
import time

timeout_for_process_file = 10


def parse_variables(smt_file_content):
    """Parse integer variables from the SMT-LIB file content using Z3."""
    # First collect original piped names
    import re
    piped_vars = set()

    # Find all piped variable names from declarations
    for match in re.finditer(r'\(declare-fun (\|[^|]+\|)', smt_file_content):
        piped_vars.add(match.group(1))

    # Parse normally with Z3
    solver = z3.Solver()
    smt_formula = z3.parse_smt2_string(smt_file_content)
    solver.add(smt_formula)
    variables = set()

    # Collect variables
    for assertion in smt_formula:
        for var in z3.z3util.get_vars(assertion):
            if var.sort() == z3.IntSort() or var.sort() == z3.RealSort():
                name = var.decl().name()
                # If this name exists in our piped variables, use the piped version
                piped_name = f"|{name}|"
                if piped_name in piped_vars:
                    variables.add(piped_name)
                else:
                    variables.add(name)

    # return variables

    print(variables)

    return list(variables)


def run_with_timeout(func, timeout, *args, **kwargs):
    def wrapper(queue, *args, **kwargs):
        result = func(*args, **kwargs)
        queue.put(result)

    queue = multiprocessing.Queue()
    process = multiprocessing.Process(
        target=wrapper, args=(queue, *args), kwargs=kwargs)
    process.start()
    process.join(timeout)

    if process.is_alive():
        process.terminate()
        process.join()
        return "Function timed out"
    else:
        return queue.get()


def add_constraints(variables, bound):
    """Create constraints for the given variables with the specified bound."""
    constraints = []
    for var in variables:
        constraints.append(f"(assert (> {var} (- {bound})))")
        constraints.append(f"(assert (< {var} {bound}))")
    return "\n".join(constraints)


def process_file(input_file, output_file, bound):
    """Process the input SMT-LIB file and write the bounded constraints to the output file."""
    if not input_file.endswith('.smt2'):
        input_file += '.smt2'
        input_file = "QF_LIA_" + input_file
    # if input file does not exist, return
    if not os.path.exists(input_file):
        print(f"File {input_file} does not exist.")
        return
    with open(input_file, 'r') as f:
        smt_content = f.read()

    variables = parse_variables(smt_content)
    new_constraints = add_constraints(variables, bound)

    # Insert the new constraints before the final (check-sat) statement
    smt_content = smt_content.replace(
        '(check-sat)', f'{new_constraints}\n(check-sat)')

    with open(output_file, 'w') as f:
        f.write(smt_content)

    print(f"Processed file saved as {output_file}")
# def process_file(input_file, output_file, bound):
#     # Placeholder for file processing logic
#     with open(input_file, 'r') as infile, open(output_file, 'w') as outfile:
#         for line in infile:
#             outfile.write(line.replace('VAR_BOUND', str(bound)))
#     print(f"Processed file saved as {output_file}")


def process_list(file_list, bounds):
    bounded_folder = 'bounded'
    os.makedirs(bounded_folder, exist_ok=True)

    if len(file_list) > 1500:
        file_list = random.sample(file_list, 1500)

    for file in file_list:
        for bound in bounds:
            output_file = os.path.join(
                bounded_folder, f"{os.path.basename(file)}_bounded_{bound}.smt2")
            if os.path.exists(output_file):
                print(f"File {output_file} already exists. Skipping...")
                continue

            # run process_file function with maximum 5 seconds timeout
            run_with_timeout(process_file, 10, file, output_file, bound)
            # process_file(file, output_file, bound)
            if os.path.exists(output_file):
                print(f"Processed file saved as {output_file}")
            else:
                print(f"Failed to process file {file} with bound {bound}")


def main():
    parser = argparse.ArgumentParser(
        description='Add constraints to SMT-LIB file.')
    parser.add_argument('--bound', type=int,
                        help='The bound for the variables.')
    parser.add_argument('--list', type=str,
                        help='File containing list of SMT-LIB files.')
    parser.add_argument('filename', type=str, nargs='?',
                        help='The input SMT-LIB file.')

    args = parser.parse_args()

    if args.list:
        with open(args.list, 'r') as list_file:
            file_list = [line.strip() for line in list_file if line.strip()]
        print(f"Processing {len(file_list)} files...")
        bounds = [5, 10, 20, 30, 50, 60, 100]
        bounds = [100,1000,10000]
        process_list(file_list, bounds)
    elif args.filename and args.bound is not None:
        input_file = args.filename
        bound = args.bound
        if input_file.endswith('.smt2'):
            input_file = input_file[:-5]
        output_file = f"{input_file}_bounded_{bound}.smt2"
        process_file(input_file, output_file, bound)
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
