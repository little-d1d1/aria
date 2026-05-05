import os
import subprocess
import sys
from .global_storage import gbl
from .utils import log

def read_vertices_file(file_path):
    """
    Reads a vertices file and calculates the range of values for each dimension.

    Parameters:
        file_path (str): Path to the vertices.txt file.

    Returns:
        list of tuples: Each tuple contains (min_value, max_value) for each dimension.
    """
    vertices = []

    try:
        with open(file_path, 'r') as file:
            is_reading_vertices = False

            for line in file:
                line = line.strip()

                # Begin reading vertices after "begin" keyword
                if line.lower() == "begin":
                    is_reading_vertices = True
                    continue

                # Stop reading vertices after "end" keyword
                if line.lower() == "end":
                    is_reading_vertices = False
                    break

                # Skip non-vertex data
                if not is_reading_vertices or line.startswith("*") or "rational" in line or "real" in line:
                    continue

                # Parse vertex lines
                if line:
                    parts = line.split()
                    if len(parts) > 1:
                        try:
                            vertices.append(list(map(float, parts[1:])))
                        except ValueError:
                            raise ValueError(
                                f"Invalid numeric data in line: {line}")

        if not vertices:
            raise ValueError("No vertices found in the file.")

        # Transpose the vertices to calculate ranges for each dimension
        dimensions = zip(*vertices)
        ranges = [(min(dim), max(dim)) for dim in dimensions]

        return ranges

    except Exception as e:
        print(f"Error reading the file: {e}")
        return []


def calculate_and_sort_ranges(ranges, decompose_lim):
    lengths = [(i, r[1] - r[0] + 1, r[1], r[0]) for i, r in enumerate(ranges)]
    lengths.sort(key=lambda x: x[1])

    selected_dimensions = []
    product = 1

    for dim, length, maxr, minr in lengths:
        if length == 0:
            continue
        if product * length < decompose_lim:
            # Dim + 1 for 1-based indexing
            selected_dimensions.append((dim + 1, length, maxr, minr))
            product *= length
        else:
            break
    log(
        f"c Number of dimensions decomposed: {len(selected_dimensions)} out of {len(ranges)}", 1)
    return selected_dimensions


def convert_latte_to_vertices(latte_filename):
    # run ~/latte/bin/latte2ext <  latte_filename > latte.ext
    cdd_output = None
    latte2ext_command = os.path.expanduser("~/latte/bin/latte2ext")
    latte_ext_filename = latte_filename[:latte_filename.rfind('.')] + '.ext'
    try:
        with open(latte_ext_filename, 'w') as f:
          cdd_output = subprocess.run([latte2ext_command], stdin=open(
              latte_filename, 'r'), stdout=f, check=True, text=True)
    except subprocess.CalledProcessError as e:
        print(f"An error occurred: {e}", file=sys.stderr)
        sys.exit(1)

    # run cddexec --rep < latte.ext
    cddexec_command = os.path.expanduser("cddexec")
    with open('cdd_output.txt', 'w') as cdd_output_file:
      cdd_output = subprocess.run(
          f"{cddexec_command} --rep < {latte_ext_filename}", shell=True, stdout=subprocess.PIPE, check=True, text=True)
      if gbl.verbosity > 4:
          print(cdd_output.stdout)
      cdd_output_file.write(cdd_output.stdout)
    # cdd_output = subprocess.run([]
    #                             f"{cddexec_command} --rep < {latte_ext_filename}", shell=True, stdout=subprocess.PIPE, check=True, text=True)
    return 'cdd_output.txt'


def get_dimension_range_from_vertices(dimension_ranges, decompose_lim):
    for i, (min_val, max_val) in enumerate(dimension_ranges):
        log(f"Dimension {i + 1}: Min = {min_val}, Max = {max_val}", 3)

    sorted_dimensions = calculate_and_sort_ranges(
        dimension_ranges, decompose_lim)
    log("Dimensions sorted by length with product < limit:", 2)
    for dim, length, _, _ in sorted_dimensions:
        log(f"Dimension {dim}: Length = {length}", 2)
    return sorted_dimensions


def get_ranges_for_besr_dimensions(latte_filename, decompose_lim):
    vertices_file = convert_latte_to_vertices(latte_filename)
    dimension_ranges = read_vertices_file(vertices_file)
    sorted_dimensions = get_dimension_range_from_vertices(
        dimension_ranges, decompose_lim)
    return sorted_dimensions


def generate_polytope_files(input_file, dimensions, output_dir):
    """
    Generate polytope files with additional constraints and store their filenames.

    Args:
        input_file (str): Path to the original polytope file.
        dimensions (list): List of tuples containing (dimension, max, min).
        output_dir (str): Directory to save generated files.

    Returns:
        list: List of filenames of the generated files.
    """
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # Read the original polytope file
    with open(input_file, 'r') as f:
        original_lines = f.readlines()

    # Get the total number of variables from the first line of the file
    header_parts = original_lines[0].split()
    num_variables = int(header_parts[1]) - 1

    file_counter = 1
    filenames = []

    def get_possible_values(dim):
        min_value, max_value = int(dim[3]), int(dim[2])
        step = 1  # Adjust the step size as needed for granularity
        return [min_value + step * i for i in range((max_value - min_value) // step + 1)]

    # Generate all combinations of values for each dimension
    from itertools import product
    all_possible_values = [get_possible_values(dim) for dim in dimensions]
    all_combinations = list(product(*all_possible_values))

    for combination in all_combinations:
        added_constraints = []
        new_lines = original_lines.copy()

        # Update the first line to reflect the new number of constraints
        first_line_parts = new_lines[0].split()
        original_constraint_count = int(first_line_parts[0])
        total_constraints = original_constraint_count + len(combination)
        first_line_parts[0] = str(total_constraints)
        new_lines[0] = " ".join(first_line_parts) + "\n"

        for i, value in enumerate(combination):
            dimension = dimensions[i][0]
            # Create the constraint line: value as constant, coefficients for all variables
            coefficients = ["-1" if j + 1 ==
                            dimension else "0" for j in range(num_variables)]
            constraint_line = f"{int(value)} " + " ".join(coefficients) + "\n"
            added_constraints.append(len(new_lines))
            new_lines.append(constraint_line)

        # Add linearity information at the end
        linearity_line = f"linearity {len(added_constraints)} " + " ".join(
            map(str, [num for num in added_constraints])) + "\n"
        new_lines.append(linearity_line)

        # Write to a new file
        filename = os.path.join(output_dir, f"polytope_{file_counter}.txt")
        with open(filename, 'w') as outfile:
            outfile.writelines(new_lines)

        filenames.append(filename)
        file_counter += 1

    return filenames


def decompose_polytope(latte_filename, decompose_lim):
    sorted_dimenstions = get_ranges_for_besr_dimensions(
        latte_filename, decompose_lim)
    filenames = generate_polytope_files(
        latte_filename, sorted_dimenstions, "output")
    log(f"Generated {len(filenames)} decomposed polytope files.", 1)
    return filenames

    exit(0)
