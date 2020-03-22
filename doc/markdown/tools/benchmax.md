# Benchmax {#benchmax}

Benchmax is a tool for automated benchmarking.
Though it was developed and is primary used for testing SMT solvers, it aims to be agnostic of the tools and formats as good as possible.

Its fundamental model is to load a list of tools and a list of benchmarks, run every tool with every benchmark, obtain the results and output all the results. While the benchmarks are fixed to a single file, we allow to choose between different [tool interfaces](@ref tools), [execution backends](@ref backends) and output formats.

## Tools {#tools}

A tool represents a binary that can be executed on some input files.
It is responsible for deciding whether it can be applied to some given file, building a command line to execute it and retrieve additional results from stdout or stderr.

The generic tool class benchmax::Tool can be used as a default.
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


### SSHBackend

The [SSHBackend](@ref benchmax::SSHBackend) can be used if you have multiple workers that can be reached via ssh (essentially a cluster without a batch job system). It allows to configure one or more computing nodes and manually schedules all the jobs on the different computing nodes.


### CondorBackend (unstable)

The [CondorBackend](@ref benchmax::CondorBackend) is aimed at the HTCondor batch system and works similar to the SlurmBackend. Note however that this backend is not well tested and we therefore consider it unstable.