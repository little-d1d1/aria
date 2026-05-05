import sys
import math
import random
import pandas as pd

from .utils import *
from .global_storage import gbl
from .latte_runner import run_volesti_on_matrix, run_volesti_sampling_on_matrix, run_tool_on_matrix
from .polytope_bv import Polytope


def volume_of_polytope(polytopefile, epsilon_prime, delta_prime):
    log(f"Calculating volume of polytope {polytopefile}", 3)
    result = 0
    if gbl.exactvolume:
        result = run_tool_on_matrix(
            polytopefile, toolname="latteintegrate")
    else:
        result = run_volesti_on_matrix(polytopefile, epsilon_prime)
    return result


def create_all_polytope_filenames(num):
    filenames = []
    random_prefix = ''.join(random.choice(string.ascii_letters)
                            for _ in range(8))
    for i in range(num):
        filename = f"{random_prefix}_cube{i+1}.ine"
        filenames.append(filename)
    log(f"{gbl.time()} Created {len(filenames)} polytope files", 2)
    return filenames

def generate_samples(polytopefile, n, precision):
    if n > 2:
      log(f"Generating samples for polytope {polytopefile}", 3)
    result = run_volesti_sampling_on_matrix(polytopefile, n)
    return result


def get_precision_from_cubes(dim,cubes):
    facet = len(cubes[0])
    precision = 1
    for cube in cubes:
        precision_this = math.ceil(8*dim*math.sqrt(math.log(facet)))
        if precision_this > precision:
            precision = precision_this
    return precision

def process_cubes_nondisjoint(cubes, mapping):
  np.random.seed(gbl.seed)
  random.seed(gbl.seed)
  mvc_eps = gbl.epsilon / 2
  volume_eps = gbl.epsilon * gbl.volepsfrac  / 2
  delta = gbl.delta
  numcubes = len(cubes)
  filenames = create_all_polytope_filenames(numcubes)
  dimensions = len(mapping.constraint_matrix.columns)
  if gbl.exactvolume:
    mvc_eps = gbl.epsilon
  thresh = max(12*math.log(24.0/delta)/(mvc_eps**2), 6.0 *
               (math.log(6.0/delta) + math.log(numcubes)))
  log(f"{gbl.time()} Starting Union Algorithm, Threshold: {thresh}", 2)
  p = 1
  # X = [[float(format(0, ".3f")) for _ in range(dimensions)] for _ in range(int(thresh))]
  X = []
  polytopes = []
  volumes = []
  S = []
  max_volume = 0
  num_zero_volume = 0
  dimensions = 2
  precision = get_precision_from_cubes(dimensions, cubes)

  log(f"{gbl.time()} Getting volumes for {numcubes} cubes", 1)

  for i in range(numcubes):
    polytope = Polytope.create_polytope_from_cube(
        cubes[i], mapping, filenames[i])
    volume = volume_of_polytope(filenames[i], volume_eps, delta)
    if volume <= 0:
      log(f"Volume of polytope is zero, skipping", 2)
      num_zero_volume += 1
      continue
    polytopes.append(polytope)
    volumes.append(volume)
    if volume > max_volume:
      max_volume = volume

  log(f"{gbl.time()} Got volumes for {numcubes} cubes", 1)

  if num_zero_volume > 0:
    log(f"Skipping {num_zero_volume} polytopes out of {numcubes} where volume is zero", 2)

  # numeffectivecubes = len(volumes)
  # i = 0
  # current_len = len(volumes)
  # while i < current_len:
  #   if volumes[i] <= max_volume * 0.001:
  #     log(f"Volume of polytope {i} is negligible ({volumes[i]}), skipping", 2)
  #     volumes.pop(i)
  #     polytopes.pop(i)
  #   else:
  #     i += 1
  #   current_len = len(volumes)
  # if len(volumes) < numeffectivecubes:
  #   log(f"Skipping {numeffectivecubes - len(volumes)} polytopes out of {numeffectivecubes} where volume is negligible", 2)

  # num_remove_inside = 0
  # num_remove_poiss_1 = 0
  # num_remove_poiss_2 = 0

  for i in range(len(polytopes)):
    polytope = polytopes[i]
    volume = volumes[i]
    log(f"--- {gbl.time()} Processing cube {i+1}/{len(polytopes)}", 2)
    if volume <= 0:
      log(f"Volume of polytope is zero, skipping", 2)
      continue
    prevXlen = len(X)
    X = [s for s in X if not polytope.is_in_polytope(s)]
    log(f"Volume of polytope: {volume}", 2)
    log(
        f"Number of points in X: {len(X)}, removed {prevXlen - len(X)}  [inside this polytope]", 2)
    prevXlen = len(X)
    while (p*volume) > thresh:
      X = [s for s in X if random.random() >= 0.5]
      p = p/2
    log(f"Number of points in X: {len(X)}, removed {prevXlen - len(X)} [make p ({p}) < thresh/vol]", 2)
    prevXlen = len(X)
    N = np.random.poisson(p*volume)
    while (N + len(X)) > thresh:
      X = [s for s in X if random.random() >= 0.5]
      p = p/2
      N = np.random.poisson(p*volume)
    log(f"Number of points in X: {len(X)}, removed {prevXlen - len(X)} [make N + |X| < thresh]", 2)
    if N == 0:
      log(f"Number of samples asked for is zero, skipping", 2)
      continue
    S = generate_samples(filenames[i], N, precision)
    if S is None:
      log(f"Sampling failed for polytope {i+1}, skipping!!!", 2)
      continue
    X.extend(S)
    log(f"Number of point in X: {len(X)} samples added: {N}", 2)

  return len(X)/(p)


def process_cubes_bringmann_friedrich(cubes, mapping, use_abboud=False):
  np.random.seed(gbl.seed)
  random.seed(gbl.seed)
  algo_name = "Abboud et al." if use_abboud else "Bringmann-Friedrich"
  numcubes = len(cubes)
  # if use_abboud:
  volume_eps = gbl.epsilon * gbl.epsilon  / (numcubes * 47)
  # else:
    # volume_eps = gbl.epsilon  / 100
  log(f"Using volume epsilon: {volume_eps}",2)
  bf_eps = (gbl.epsilon - volume_eps) / (1+ volume_eps)
  log(f"Using {algo_name} algorithm with eps_tilde = {bf_eps}",2)

  c_tilde = (1 + volume_eps)**2  / (1 - volume_eps)
  log(f"Using c_tilde = {c_tilde}",2)
  if use_abboud:
    thresh = 8 * math.log(8/gbl.delta) * (1 + bf_eps) * numcubes / ((bf_eps**2) - 8 * (c_tilde -1)*numcubes)
  else:
    thresh = 24 * math.log(2) * (1 + bf_eps) * numcubes / ((bf_eps**2) - 8 * (c_tilde -1)*numcubes)
  assert thresh > 0, f"Threshold for {algo_name} algorithm is non-positive, increase epsilon or decrease number of cubes"
  log(f"Threshold for {algo_name} algorithm: {thresh}",2)
  delta = gbl.delta
  filenames = create_all_polytope_filenames(numcubes)
  dimensions = len(mapping.constraint_matrix.columns)
  if gbl.exactvolume:
    bf_eps = gbl.epsilon
  log(f"{gbl.time()} Starting Union Algorithm, Threshold: {thresh}", 2)
  p = 1
  # X = [[float(format(0, ".3f")) for _ in range(dimensions)] for _ in range(int(thresh))]
  X = []
  polytopes = []
  volumes = []
  S = []
  max_volume = 0
  num_zero_volume = 0
  dimensions = 2
  precision = get_precision_from_cubes(dimensions, cubes)

  log(f"{gbl.time()} Getting volumes for {numcubes} cubes", 1)
  sum_volume = 0
  for i in range(numcubes):
    polytope = Polytope.create_polytope_from_cube(
        cubes[i], mapping, filenames[i])
    volume = volume_of_polytope(filenames[i], volume_eps, delta)
    if volume <= 0:
      log(f"Volume of polytope is zero, skipping", 2)
      num_zero_volume += 1
      continue
    polytopes.append(polytope)
    volumes.append(volume)
    sum_volume += volume
    if volume > max_volume:
      max_volume = volume

  cube_probabilities = [vol/sum_volume for vol in volumes]

  log(f"{gbl.time()} Got volumes for {numcubes} cubes", 1)

  if num_zero_volume > 0:
    log(f"Skipping {num_zero_volume} polytopes out of {numcubes} where volume is zero", 2)
  tries = 0
  M = 0
  repeats_done = False
  while not repeats_done:
    i = random.choices(range(len(cube_probabilities)), weights=cube_probabilities, k=1)[0]
    S = generate_samples(filenames[i], 1, precision)
    assert S is not None
    M += 1
    S_inj = False
    while S_inj is False:
      if tries > thresh:
        repeats_done = True
        break
      j = random.choices(range(len(cube_probabilities)), k=1)[0]
      polytope = polytopes[j]
      assert polytope is not None
      tries += 1
      if tries % 50 == 0:
        log(f"Tries: {tries}, M: {M}",2)
      if polytope.is_in_polytope(S[0]):
        S_inj = True
  res = thresh * sum_volume / (numcubes * M)
  log(f"Total Tries {tries} for M {M}",2)
  return res
