import random
import argparse
from z3 import *


def generate_smt_lib(n_vars, seed, prob, ratio, max_val):
    random.seed(seed)

    # Create variable symbols
    variables = [Int(f"x{i}") for i in range(n_vars)]

    # Generate random constraints
    constraints = []
    num_constraints = int(ratio * n_vars)
    for _ in range(num_constraints):
        coeffs = [random.randint(-max_val, max_val) if random.random()
                  < prob else 0 for _ in range(n_vars)]
        rhs = random.randint(-max_val, max_val)
        lhs = sum(coeff * var for coeff,
                  var in zip(coeffs, variables) if coeff != 0)

        # # Skip constraints with no variables
        # if not lhs.decl():
        #     continue

        if random.choice([True, False]):
            constraints.append(lhs <= rhs)
        else:
            constraints.append(lhs >= rhs)

    # Prepare the SMT-LIB script
    smt_script = "(set-logic QF_LIA)\n"
    for var in variables:
        smt_script += f"(declare-fun {var.decl().name()} () Int)\n"

    for constraint in constraints:
        smt_script += f"(assert {constraint.sexpr()})\n"

    smt_script += "(check-sat)\n"

    # Save to file
    filename = f"cube_var_{n_vars}_seed_{seed}_prob_{prob}_ratio_{ratio}_max_{max_val}.smt2"
    with open(filename, "w") as file:
        file.write(smt_script)

    print(f"SMT-LIB script written to {filename}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate random SMT-LIB constraints.")
    parser.add_argument("--vars", type=int, default=5,
                        help="Number of variables")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--prob", type=float, default=0.5,
                        help="Probability of a variable appearing in a constraint")
    parser.add_argument("--ratio", type=float, default=2.0,
                        help="Ratio of the number of constraints to the number of variables")
    parser.add_argument("--max_val", type=int, default=5,
                        help="Maximum absolute value for coefficients and RHS (minimum is the negative of this)")

    args = parser.parse_args()

    generate_smt_lib(args.vars, args.seed, args.prob,
                     args.ratio, args.max_val)
