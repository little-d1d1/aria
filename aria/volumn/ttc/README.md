# TTC: Toolbox for Theory Counting

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![CI](https://github.com/meelgroup/ttc/actions/workflows/ci.yml/badge.svg)](https://github.com/meelgroup/ttc/actions/workflows/ci.yml)

ttc is a volume computation for SMT (LRA) formulas. Given an LRA formula, ttc returns the volume of the solution space with $(\varepsilon,\delta)$-guarantees. Find more details in our [KR 2025 paper](https://arxiv.org/abs/2508.09934).

## Installation
ttc is available for macOS and linux. The easiest method to install and use ttc is to use pipx.

### Quick install via pipx

Requires Python 3.11 and `pipx`

```bash
sudo apt install python3.11 python3.11-venv
brew install python@3.11 gmp
```

```sh
python3 -m pip install --user pipx setuptools
python3 -m pipx ensurepath
```

Now install ttc using `pipx`.

```sh
pipx install --python python3.11 git+https://github.com/meelgroup/ttc.git
```

ttc is ready for usage like:

```sh
ttc example/box_or_lra.smt2
```

First invocation of ttc downloads prebuilt binaries and dependency wheels; subsequent runs start instantly.

For other methods to build ttc, follow instructions from [utils/install.md](https://github.com/meelgroup/ttc/blob/main/utils/install.md).

## Usage

The expected input format is the [SMT-LIB2](https://smtlib.cs.uiowa.edu/language.shtml) format. The tool supports the theory of linear real arithmetic (QF_LRA). See `example` directory for some examples.

```sh
ttc example/box_or_lra.smt2
```

Output includes a line of the form:

```
s vol <float>
```

For all options: `./ttc --help`

### Guarantees

ttc provides so-called "PAC", or Probably Approximately Correct, guarantees. The system guarantees that the solution found is within a certain tolerance (called "epsilon") with a certain probability (called "delta"). The default tolerance and probability, i.e. epsilon and delta values, are set to 0.8 and 0.2, respectively. Both values are configurable.

### Issues, questions, bugs, etc.

Please click on "issues" at the top and [create a new issue](https://github.com/meelgroup/ttc/issues/new).

## How to Cite

This work is by Arijit Shaw, Uddalok Sarkar, and Kuldeep S. Meel, as [published in KR-25](https://arxiv.org/abs/2508.09934).

The benchmarks used in our evaluation can be found [here](https://zenodo.org/records/16782811).