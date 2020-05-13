# Benchmax {#benchmax}

Benchmax is a tool for automated benchmarking.
Though it was developed and is primary used for testing SMT solvers, it aims to be agnostic of the tools and formats as good as possible.

Its fundamental model is to load a list of tools and a list of benchmarks, run every tool with every benchmark, obtain the results and output all the results. While the benchmarks are fixed to a single file, we allow to choose between different [tool interfaces](@ref tools), [execution backends](@ref backends) and output formats.

## General usage

Benchmax could be called as follows:

```
./benchmax -T 1m -M 4Gi -S /path/to/smtrat-static -X out.xml -b ssh --ssh.node user@127.0.0.1@5\#9 -D /path/to/benchmark/set
```

This will run benchmax with the SMT-RAT tool at `/path/to/smtrat-static` on the `/path/to/benchmark/set` with a time limit of 1 minute and a memory limit of 4 gigabyte. The resulst will be written to `out.xml`. The execution is done on an SSH backend on localhost with 9 connections and executing 5 parallel jobs per connection.

It is recommended to use static builds to avoid issues with missing libraries.

For more information, run `./benchmax --help`.

### Collecting statistics

Some tools like SMT-RAT or Z3 can provide statistics about the solving process for each individual benchmark. By using the `-s` respectively `--statistics`, statistics are collected and stored in the output file.

#### Large output

It is recommended to aggregate statistics as much as possible inside SMT-RAT. However, if the output might get large, you might want to use `--use-tmp` to prevent benchmax running out of memory.

### Working with the results

In the SMT-RAT repository, several tools for converting the result XML file are included: `utilities/xml2ods.py` converting it to a *Flat XML LibreOffice Calc Sheet*. In `utilities/evaluation` is a small python library for importing the results into Python (or a Jupyter notebook).

## Tools {#tools}

A tool represents a binary that can be executed on some input files.
It is responsible for deciding whether it can be applied to some given file, building a command line to execute it and retrieve additional results from `stdout` or `stderr`.

The generic tool class `benchmax::Tool` can be used as a default.
It will run the given binary on any input file and benchmax records the exit code as well as the runtime.

If more information is needed a new tool class can be derived that overrides or extends the default behaviour. Some premade tools are available (and new ones should be easy to create):

- benchmax::MathSAT
- benchmax::Minisatp
- benchmax::SMTRAT
- benchmax::SMTRAT_OPB
- benchmax::Z3

## Backends {#backends}

A [backend](@ref benchmax::Backend) offers the means to run the tasks in a specific manner.
A number of different backends are implemented that allow for using benchmax in various scenarios.

### LocalBackend

The [LocalBackend](@ref benchmax::LocalBackend) can be used to execute benchmarks on a local machine easily. It does not allow for any parallelization but simply executes all tasks sequentially.


### SlurmBackend

The [SlurmBackend](@ref benchmax::SlurmBackend) employs the Slurm workload manager to run benchmarks on a cluster. It essentially collects all tasks that shall be run in a file and creates an appropriate slurm submit file. It then submits this job, waits for it to finish and collects the results from the output files.

The Slurm backend supports starting (`--mode execute`) and collecting results (`--mode collect`) separately, thus avoiding the need for running benchmax in a screen.  


### SSHBackend

The [SSHBackend](@ref benchmax::SSHBackend) can be used if you have multiple workers that can be reached via ssh (essentially a cluster without a batch job system). It allows to configure one or more computing nodes and manually schedules all the jobs on the different computing nodes.

Using `--ssh.node`, a node is specified  in the format `<user>[:<password>]@<hostname>[:<port = 22>][@<cores = 1>][#<connections = 1>]`.

By setting the flag `--ssh.resolvedeps`, dependencies (i.e. dynamic libraries) are resolved and uploaded with the solver.


### CondorBackend (unstable)

The [CondorBackend](@ref benchmax::CondorBackend) is aimed at the HTCondor batch system and works similar to the SlurmBackend. Note however that this backend is not well tested and we therefore consider it unstable.