# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

Online Resource associated with the Paper

    "More is Less: Adding Polynomials for Faster Explanations in NLSAT"
    Valentin Promies <promies@cs.rwth-aachen.de>, Jasper Nalbach <nalbach@cs.rwth-aachen.de>, Erika Ábrahám <abraham@cs.rwth-aachen.de> and Paul Wagner (all RWTH Aachen University)

## Reproducing Results

In addition to the source code of SMT-RAT including the algorithms from the paper, we provide a `Dockerfile` and the folder `artifact` for reproducing the presented results.

### Requirements
- Install [Docker](https://www.docker.com/get-started/) in case you do not have it yet.
- If you want to reproduce the plots using the provided notebook, you will also need [Jupyter Notebook](https://jupyter.org/).
- Our experiments were conducted on machines with two Intel Xeon 8468 Sapphire CPUs (2.1 GHz per core). When comparing results, keep possible hardware differences in mind, as well as the effect of running the tools in Docker.

### Running Tests

1. **Building the image.**
    You can build the provided Docker image by running in this folder the following command (This takes about 30-60 minutes).
    ```
    docker build -f "Dockerfile" -t artifact:latest .
    ```

2. **Running the image.**
    ```
    docker run --rm -it artifact:latest
    ```
    This should start a shell in the respective container.
    In the working directory in the container, you can find
    - the executables in the folder `tools`
    - the benchmark inputs `QF_NRA`
    - the test scripts `run_tests.py` and `run_tests_util.py`
    - the stats collected for the paper in `stats.csv`

3. **Running the test script.**
    In the Docker container, you can run
    ```
    python3 run_tests.py
    ```
    to run all tools on 5 randomly selected inputs.
    To change the sample size to some number `n`, call
    ```
    python3 run_tests.py <n>
    ```
    Note that this can take up to `11*n minutes`, so it is advised to keep the sample size small.

### Reproducing plots and numbers

We provide a jupyter notebook (`artifact/analysis.ipynb`) which lets you reproduce the plots and numbers shown in the paper.
It also gives an idea on how to work with the data collected in `stats.csv` for further analysis.


