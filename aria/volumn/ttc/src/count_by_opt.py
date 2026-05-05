import numpy as np
from scipy.optimize import minimize
from .polytope_operations import canonicalize, read_h_representation, get_A_b_from_array
from .utils import log


def objective(zeta: np.ndarray) -> float:
    """Objective function (to be maximized) evaluated at zeta.

    The function is defined as:
        f(zeta) = sum_j [ (zeta_j + 1)*log(zeta_j + 1) - zeta_j*log(zeta_j) ]
    Since SciPy minimizes, we return the negative of f(zeta).

    Args:
        zeta (np.ndarray): A 1D numpy array of positive tilting parameters.

    Returns:
        float: The negative of the objective function value.
    """
    # Ensure numerical stability
    zeta = np.maximum(zeta, 1e-12)
    val = np.sum((zeta + 1) * np.log(zeta + 1) - zeta * np.log(zeta))
    return -val


def count_by_optimization(A: np.ndarray,
                          b: np.ndarray,
                          num_samples: int = 10000,
                          tol: float = 1e-5) -> float:
    """
    Estimate the number of integer points in a polytope defined by an H-representation.

    The polytope is given by:
        P = { x in R^n : A x <= b }
    where A is an (m x n) matrix and b is a vector of length m.

    The algorithm uses a two-step process:
      1. Optimal Tilting via Convex Optimization:
      2. Importance Sampling with Geometric Distributions:

    Args:
        A (np.ndarray): 2D array of shape (m, n) representing the coefficients of the inequalities.
        b (np.ndarray): 1D array of length m representing the right-hand side of the inequalities.
        num_samples (int): Number of random samples used for importance sampling.
        tol (float): Tolerance added to inequality checks for numerical stability.

    Returns:
        float: An estimate of the number of integer points within the polytope.

    Raises:
        ValueError: If the optimization does not converge or no feasible point is found.
    """
    m, n = A.shape

    # Define the constraints for SLSQP: For each row i, we need A[i] @ zeta <= b[i]
    constraints = [{
      'type': 'ineq',
      'fun': lambda z, A=A, b=b, i=i: b[i] - np.dot(A[i], z)
    } for i in range(m)]

    # Set bounds for each variable: zeta_j > 0
    bounds = [(1e-6, None)] * n

    # Choose an initial feasible guess. Here we start with a small positive value.
    zeta0 = np.full(n, 0.1)

    print("Starting optimization for tilting parameters...")
    # Run the optimization to minimize the negative objective.
    result = minimize(objective, zeta0, method='SLSQP',
              bounds=bounds, constraints=constraints)
    if not result.success:
      raise ValueError("Optimization failed: " + result.message)

    zeta_opt = result.x
    print("Optimization successful. Optimal tilting parameters:", zeta_opt)

    # Compute the optimal objective value f(ζ)
    f_value = np.sum((zeta_opt + 1) * np.log(zeta_opt + 1) - zeta_opt * np.log(zeta_opt))
    print("Computed optimal objective value:", f_value)

    # Importance sampling: sample each coordinate from a geometric distribution.
    # p_j = 1 / (ζ_j + 1), and np.random.geometric returns samples in {1, 2, ...}.
    samples = np.zeros((num_samples, n), dtype=int)
    for j in range(n):
      p_j = 1.0 / (zeta_opt[j] + 1)
      samples[:, j] = np.random.geometric(p_j, size=num_samples) - 1  # Adjust to 0-indexed

    print("Performing importance sampling...")
    # Check which samples satisfy A*x <= b (with a small tolerance)
    valid = np.all((A @ samples.T) <= (b.reshape(-1, 1) + tol), axis=0)
    alpha = np.mean(valid)
    print("Fraction of valid samples (alpha):", alpha)

    # Final estimate: alpha * exp(f_value)
    estimate = alpha * np.exp(f_value)
    print("Final estimated count:", estimate)
    return estimate


def count_by_optimization_matrix(filepath):
  canonicalized_file = canonicalize(filepath, ignore_lin_set=False)
  log(f"Canonicalized file: {canonicalized_file}", 2)
  if canonicalized_file == -1:
    return 0
  array = read_h_representation(canonicalized_file)
  A, b = get_A_b_from_array(array)
  # print(A, b)
  # with open(filepath, 'r') as file:
  #     lines = file.readlines()
  #     m, n = map(int, lines[0].strip().split()[:2])
  #     A = []
  #     b = []
  #     for line in lines[1:]:
  #         values = list(map(int, line.strip().split()))
  #         b.append(values[0])
  #         A.append(values[1:])
  #         A[-1] = [-x for x in A[-1]]
  #     A = np.array(A)
  #     b = np.array(b)
  #     print(A, b)
  return count_by_optimization(A, b)



if __name__ == '__main__':
    # Example usage: Define a 2D polytope in H-representation.
    A = np.array([[1, 2],
                  [-1, 2],
                  [0, -1]])
    b = np.array([4, 2, 0])

    estimated_count = count_by_optimization(A, b, num_samples=10000)
    print(
        f"Estimated number of integer points in the polytope: {estimated_count}")
