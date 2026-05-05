import cdd
from .utils import log
from pprint import pprint
import numpy as np
from .global_storage import gbl
"""
This module provides functions to read, write, and canonicalize H-representations of polytopes.

Functions:
  read_h_representation(file_name):
    Reads an H-representation from a file in latte format.
    Args:
      file_name (str): The name of the file to read from.
    Returns:
      list: A list of lists representing the H-representation.

  write_h_representation(file_name, array):
    Writes an H-representation to a file in latte format.
    Args:
      file_name (str): The name of the file to write to.
      array (list): A list of lists representing the H-representation.

  canonicalize(input_file):

"""
from pprint import pprint

def read_h_representation(file_name):
    with open(file_name, 'r') as file:
        array = []
        rows, cols = 0, 0
        for line in file:
            if line.strip() and line.split()[0].replace('-', '', 1).replace('.', '', 1).isdigit():
              if rows == 0 and cols == 0:
                  nums = line.split()[:2]
                  rows, cols = map(int, nums)
              else:
                  array.append([float(num) for num in line.split()])
    if len(array) != rows:
        print(f"Warning: expected {rows} rows from input, got {len(array)} rows")
    if len(array[0]) != cols:
        print(f"Warning: expected {cols} columns from input, got {len(array[0])} columns")

    return array

def get_A_b_from_array(array):
    A = []
    b = []
    for row in array:
        b.append(row[0])
        A.append(row[1:])
        A[-1] = [-x for x in A[-1]]
    A = np.array(A)
    b = np.array(b)
    return A, b

def write_h_representation(file_name, array, lin_set, ignore_lin_set=False):
    if len(lin_set) > 0 and not ignore_lin_set:
        log(f"Warning: exists {len(lin_set)} equalities, d-dim volume is zero for this polytope", 2)
        return 0
    with open(file_name, 'w') as file:
      file.write("H-representation\n")
      file.write("begin\n")
      file.write(f"{len(array)} {len(array[0])} rational\n")
      for i in range(len(array)):
          row = array[i]
          if i not in lin_set:
            file.write(' '.join(map(str, row)) + '\n')
      file.write("end\n")

def canonicalize(input_file, ignore_lin_set=False):
    """
    Canonicalizes an H-representation read from a file in latte format and writes the result to a file in ine format. Uses cddlib for this purpose.
    If there exists any equality constraints in the input H-representation, the function will return 0 and print a warning message. TODO In future, we may add support for handling equality constraints.
    if ignore_lin_set is True, then the function will ignore the lin_set and continue with the canonicalization without checking for inequality constraints.
    Args:
        input_file (str): The name of the input file containing the H-representation in latte format.
    Returns:
        str: The name of the output file containing the canonicalized H-representation in ine format.
    """
    array = read_h_representation(input_file)

    mat = cdd.matrix_from_array(array, rep_type=cdd.RepType.INEQUALITY)
    # mat.rep_type = cdd.RepType.INEQUALITY

    cdd.matrix_canonicalize(mat)
    log(f"c [ttc] canonicalizing array of size \
            {len(array)}x{len(array[0])} using cddlib", 3)

    log(f"c [ttc] canonicalized array of size \
            {len(mat.array)}x{len(mat.array[0])} using cddlib", 3)

    output_file = input_file.split('.')[0] + '.can.ine'
    result = write_h_representation(output_file, mat.array, mat.lin_set, ignore_lin_set)
    if result == 0:
        return -1
    log(f"c [ttc] file {input_file} canonicalized to file {output_file}", 3)
    gbl.tempfiles.append(input_file)
    gbl.tempfiles.append(output_file)
    return output_file


