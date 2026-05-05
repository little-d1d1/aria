import numpy as np
import pandas as pd
import cdd
import polytope as pc
from z3 import *
from z3.z3util import is_bv_value
import argparse
import subprocess
from .utils import *
from .global_storage import gbl
from pprint import pprint

# TODO get simplified instance of polytope from Latte

class Polytope:
    def __init__(self, A, b):
        self.A = A
        self.b = b
        self.optbw = False
        self.shift = None
        self.smtfilename = "temp.smt2"
        self.vertices = None
        self.count = None
        self.max_coords = []
        self.equality_constraints = []
        self.solver = Solver()

    @staticmethod
    def from_file(filepath, optbw=True, shift=True):
        with open(filepath, 'r') as file:
            lines = file.readlines()
            m, n = map(int, lines[0].strip().split())
            A = []
            b = []
            for line in lines[1:]:
                values = list(map(int, line.strip().split()))
                b.append(values[0])
                A.append(values[1:])
            A = np.array(A)
            b = np.array(b)
            return Polytope(A, b)

    @staticmethod
    def create_polytope_from_cube(cube, mapping, filename = ""):
        dfd = pd.DataFrame(columns=mapping.constraint_matrix.columns)
        for literal in cube:
            if literal in [0, 1, -2]:
                continue
            # if lit is not in constraint_matrix, then show warning and exit
            if literal not in mapping.constraint_matrix.index:
                log(f"Literal {literal} not found in constraint matrix", 3)
                continue
            temp_row = mapping.constraint_matrix.loc[[literal]]
            if dfd.empty:
                dfd = temp_row
            dfd = pd.concat([dfd, temp_row])
        # drop index
        if filename != "":
            write_matrix_to_file(dfd, filename)
        new_b = dfd.iloc[:, 0].to_numpy()
        new_A = dfd.iloc[:, 1:].to_numpy()
        log(f"Created polytope from cube: \n {new_A} \n {new_b}", 4)
        return Polytope(new_A, new_b)



    def is_in_polytope(self, point):
        tol = 1e-6
        result = np.all(np.dot(-self.A, point) <= self.b + tol)
        return result



    def to_smt_bitvector(self):
        # TODO try balanced encoding
        solver = Solver()
        n = self.A.shape[1]
        bitwidth = self.determine_bitwidth()
        # TODO potential error -- wrong variables are taken?
        x = [BitVec(f'x{i}', bitwidth) for i in range(n)]
        for i in range(len(self.b)):
            if i in self.equality_constraints:
                constraint = sum(self.A[i][j] * x[j]
                                  for j in range(n)) == self.b[i]
            else:
                constraint = sum(self.A[i][j] * x[j]
                                  for j in range(n)) <= self.b[i]
            solver.add(constraint)
            # log(f"c [ttc->tobv] Adding constraint: {constraint} \n for {self.A[i]} and {self.b[i]}",3)
        for i in range(len(self.max_coords)):
            solver.add(x[i] <= self.max_coords[i])
            solver.add(x[i] > 0)
        return solver

    def to_smt_lia(self):
        n = self.A.shape[1]
        x = [Int(f'x{i}') for i in range(n)]
        for i in range(len(self.b)):
            if i in self.equality_constraints:
                constraint = sum(self.A[i][j] * x[j]
                                  for j in range(n)) == self.b[i]
            else:
                constraint = sum(self.A[i][j] * x[j]
                                  for j in range(n)) <= self.b[i]
            self.solver.add(constraint)
            # log(f"c [ttc->tobv] Adding constraint: {constraint} \n for {self.A[i]} and {self.b[i]}",3)

        return self.solver

    def to_smt_lra(self, solve=False):
        n = self.A.shape[1]
        x = [Real(f'x{i}') for i in range(n)]
        for i in range(len(self.b)):
            if i in self.equality_constraints:
                constraint = sum(self.A[i][j] * x[j]
                                 for j in range(n)) == self.b[i]
            else:
                constraint = sum(self.A[i][j] * x[j]
                                 for j in range(n)) <= self.b[i]
            self.solver.add(constraint)
            # log(f"c [ttc->tobv] Adding constraint: {constraint} \n for {self.A[i]} and {self.b[i]}",3)\
        if solve:
            if gbl.verbosity >= 5:
                tosmt = self.solver.to_smt2()
                log(f"c [ttc->tobv] Combined SMT2 constraints:\n{tosmt}", 5)
            result = self.solver.check()
            return result
        return self.solver

    def check_joint_satisfiability(self, other_polytope):
        """
        Check if the current polytope and another polytope are jointly satisfiable.
        This is done by combining their constraints and checking satisfiability.
        """
        n = other_polytope.A.shape[1]
        log(f"c [ttc->tobv] Running joint satisfiability with another polytope", 4)
        log(f"other polytope \n {other_polytope.A} \n {other_polytope.b}", 5)
        x = [Real(f'x{i}') for i in range(n)]

        self.solver.push()  # Save the current state of the solver



        # Add constraints from the second polytope
        for i in range(len(other_polytope.b)):
            if i in other_polytope.equality_constraints:
                constraint = sum(other_polytope.A[i][j] * x[j]
                                 for j in range(n)) == other_polytope.b[i]
            else:
                constraint = sum(other_polytope.A[i][j] * x[j]
                                 for j in range(n)) <= other_polytope.b[i]
            self.solver.add(constraint)

        if gbl.verbosity >= 5:
            tosmt = self.solver.to_smt2()
            log(f"c [ttc->tobv] Combined SMT2 constraints:\n{tosmt}", 5)

        result = self.solver.check()
        self.solver.pop()  # Restore the previous state
        return result

    def to_smt2_file(self, filepath, encoding = "bv"):
        if encoding == "bv":
            solver = self.to_smt_bitvector()
            f = And(solver.assertions())
            smt2_str = Z3_benchmark_to_smtlib_string(
                f.ctx_ref(), "benchmark", "QF_BV", "unknown", "", 0, None, f.as_ast())
        elif encoding == "lia":
            solver = self.to_smt_lia()
            f = And(solver.assertions())
            smt2_str = Z3_benchmark_to_smtlib_string(
                f.ctx_ref(), "benchmark", "QF_LIA", "unknown", "", 0, None, f.as_ast())
        with open(filepath, 'w') as file:
            file.write(smt2_str)



    def get_vertices(self):
        polytope_array = np.hstack((self.b[:, np.newaxis], - self.A))
        mat = cdd.matrix_from_array(polytope_array, rep_type=cdd.RepType.INEQUALITY)
        # mat.rep_type = cdd.RepType.INEQUALITY
        poly = cdd.polyhedron_from_matrix(mat)

        vertices_cdd = cdd.copy_generators(poly)

        vertices = np.array(vertices_cdd.array)
        if len(vertices) == 0:
            log("c [ttc->tobv] Polytope is empty",2)
            return None
        log(f"c [ttc->tobv] Got {len(vertices)} {len(vertices[0])-1}-dimensional vertices  from cddlib",3)
        log(f"c [ttc -> tobv] vertices are \n {vertices[:, 1:]}", 6)
        # Exclude the first column which is the homogeneous coordinate
        return vertices[:, 1:]


    def shift_to_positive_coordinates(self):
        # TODO this is not yet correct
        vertices = self.get_vertices()
        min_coords = np.floor(np.min(vertices, axis=0))

        shift_vector = - min_coords + 1

        # print("b vector before shifting:", self.b)
        # print("shift vector:", shift_vector)
        # p = pc.Polytope(self.A, self.b)
        # vertices = pc.extreme(p)
        # # print("vertices before shifting:", vertices)
        # p = p.translation(- shift_vector)
        # vertices = pc.extreme(p)
        # print("vertices after shifting:", vertices)
        log(f" polytope before shift \n {self.A} \n {self.b}", 5)
        log(f"Vertices of the polytope before shifting:\n {vertices}", 5)
        log(f"Minimum coordinate values for each dimension: {min_coords}", 5)
        log(f"Shift vector to move all coordinates to positive space: { shift_vector}", 5)

        self.b = self.b - np.dot(self.A, - shift_vector)
        # p = pc.Polytope(self.A, self.b)
        # vertices = pc.extreme(p)
        # log(f"polytopelib shifted vertices:\n {vertices}", 5)

        # TODO this check is not necessary
        vertices = self.get_vertices()
        log(f"c [ttc->tobv] vertices after shifting:\n {vertices}", 5)
        log(f"c [ttc->tobv]shifted polytope \n {self.A} \n {self.b}", 5)
        if vertices is not None:
            self.max_coords = np.ceil(np.max(vertices, axis=0))
        else:
            self.max_coords = None
        return shift_vector

    def determine_bitwidth(self):
        # TODO need to be careful about the bitwidth for the constant term
        vertices = self.get_vertices()
        if vertices is None:
            raise ValueError(
                "Vertices could not be determined by polytope library.")
        dimension = vertices.shape[1]
        max_value = np.max(np.abs(vertices))
        bitwidth = 2 * int(np.ceil(np.log2(max_value + 1))) + dimension
        log("c [ttc->tobv] Vertices ranges for each coordinate:", 4)
        for i in range(vertices.shape[1]):
            coord_values = vertices[:, i]
            log(f"c [ttc->tobv] Coordinate {i}: min = {np.min(coord_values)}, max = {np.max(coord_values)}", 4)
        log(f"c [ttc->tobv] Maximum absolute value among all vertices coordinates: {max_value}", 4)
        log(f"c [ttc->tobv] Determined bitwidth: {bitwidth}", 4)
        return bitwidth

    def canonicalize(self):
        polytope_array = np.hstack((self.b[:, np.newaxis], - self.A))
        mat = cdd.matrix_from_array(polytope_array, rep_type=cdd.RepType.INEQUALITY)

        # mat.rep_type = cdd.RepType.INEQUALITY
        cdd.matrix_canonicalize(mat)
        poly = np.array(mat.array)
        self.A = - poly[:, 1:]
        self.b = poly[:, 0]
        self.equality_constraints = mat.lin_set
        log(f"c [ttc] canonicalized array of size \
            {len(mat.array)}x{len(mat.array[0])}, {len(self.equality_constraints)} many equalities", 2)

    def run_csb_and_get_count(self):
        filename = self.smtfilename
        csb_path = os.path.join(get_bin_dir(), 'csb')

        result = subprocess.run(
            [csb_path, '-c', filename], capture_output=True, text=True)
        output_lines = result.stdout.splitlines()
        for line in output_lines:
            if line.startswith("s mc"):
                return int(line.split()[2])
        raise ValueError("Count not found in the output")

    def run_pact_and_get_count(self):
        filename = self.smtfilename
        csb_path = os.path.join(get_bin_dir(), 'cvc5')
        # TODO get exact command
        if self.max_coords is None:
            raise ValueError("max_coords is None, cannot determine maxint")
        maxint = int(max(self.max_coords))
        full_command = [
            csb_path, "-S", "--hashsm", "lia", "-i", "-m", "--no-tfp", "-t", "smap", "--maxint", str(maxint), filename
        ]
        log(f"c [ttc->tobv] Running PACT with command: {full_command}", 1)
        result = subprocess.run(
            full_command, capture_output=True, text=True)
        output_lines = result.stdout.splitlines()
        log("pact coutput", 4)
        for line in output_lines:
            log(line, 4)
            if line.startswith("s mc"):
                count = int(line.split()[2])
                print("Lattice point count:", count)
                return count
        raise ValueError("Count not found in the output")


    def count_lattice_points_smt(self, encoding="bv"):
        # polytope = Polytope.from_file(args.input_file, args.optbw, args.shift)
        if self.get_vertices() is None:
          log("c [ttc->tobv] Polytope is empty",3)
          return 0

        self.shift_to_positive_coordinates()
        self.canonicalize()
        count = -42


        if encoding == "bv":
            self.to_smt2_file(self.smtfilename, encoding)
            count = self.run_csb_and_get_count()
        elif encoding == "lia":
            self.to_smt2_file(self.smtfilename, encoding)
            log(f"c [ttc->tobv] Running PACT on {self.smtfilename}", 1)
            count = self.run_pact_and_get_count()
            log(f"c [ttc->tobv] PACT count: {count}", 1)

        print("Lattice point count:", count)
        return count

"""
    def get_chebyshev_center(self):
        p = pc.Polytope(self.A, self.b)
        return p.chebXc

    def get_radius(self):
        p = pc.Polytope(self.A, self.b)
        return p.chebR

    def check_equivalence(self):
        solver = self.to_smt_bitvector()
        n = self.A.shape[1]
        bitwidth = self.determine_bitwidth()
        x = [BitVec(f'x{i}', bitwidth) for i in range(n)]

        # Convert bitvector constraints back to polytope
        constraints = solver.assertions()
        A_bv = []
        b_bv = []
        for constraint in constraints:
            lhs = constraint.arg(0)
            rhs = constraint.arg(1)
            A_row = []
            b_value = -simplify(rhs).as_long()
            for i in range(n):
                arg = lhs.arg(i)
                if is_bv_value(arg):
                    coeff = arg.as_long()
                elif is_bv_mul(arg):
                    coeff = arg.arg(0).as_long()
                else:
                    print(f"Non-numeric argument encountered: {arg}")
                    coeff = 0
                A_row.append(coeff)
            A_bv.append(A_row)
            b_bv.append(b_value)

        A_bv = np.array(A_bv)
        b_bv = np.array(b_bv)
        polytope_bv = pc.Polytope(A_bv, b_bv)

        # Compare the original polytope with the one obtained from bitvector constraints
        original_polytope = pc.Polytope(self.A, self.b)
        return original_polytope == polytope_bv

# Example usage
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Process a polytope file.')
    parser.add_argument('input_file', type=str, help='Path to the input file')
    parser.add_argument('output_file', type=str, nargs='?', default='output.smt2',
                        help='Path to the output SMT2 file (default: output.smt2)')
    parser.add_argument('--shift',  action='store_true',
                        help='Shift the polytope by given vector')
    parser.add_argument('--optbw', action='store_true',
                        help='Optimize bitwidth based on dimension range')

    args = parser.parse_args()

    polytope = Polytope.from_file(args.input_file, args.optbw, args.shift)

    if args.shift:
        shift_vector = polytope.shift_to_positive_coordinates()
        print("Shift vector to positive coordinates:", shift_vector)

    vertices = polytope.get_vertices()
    chebyshev_center = polytope.get_chebyshev_center()
    chebyshev_radius = polytope.get_radius()
    print("Vertices:", vertices)
    print("Chebyshev Center:", chebyshev_center)
    print("Chebyshev Radius (outscribe):", chebyshev_radius)
    polytope.to_smt2_file(args.output_file)
    print(f"SMT2 file {args.output_file} generated.")
    count = polytope.count_lattice_points()
    print(f"Lattice point count: {count}")

    # equivalent = polytope.check_equivalence()
    # print(
    #     f"Bitvector constraints are equivalent to the input polytope: {equivalent}")
"""