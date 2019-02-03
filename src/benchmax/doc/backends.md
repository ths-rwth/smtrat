Backends {#backends}
====================

A backend offers the means to run the tasks in a specific manner.
A number of different backends are implemented that allow for using benchmax in various scenarios.

LocalBackend
------------

The [LocalBackend](@ref benchmax::LocalBackend) can be used to execute benchmarks on a local machine easily. It does not allow for any parallelization but simply executes all tasks sequentially.


SlurmBackend
------------

The [SlurmBackend](@ref benchmax::SlurmBackend) employs the Slurm workload manager to run benchmarks on a cluster. It essentially collects all tasks that shall be run in a file and creates an appropriate slurm submit file. It then submits this job, waits for it to finish and collects the results from the output files.


SSHBackend
----------

The [SSHBackend](@ref benchmax::SSHBackend) can be used if you have multiple workers that can be reached via ssh (essentially a cluster without a batch job system). It allows to configure one or more computing nodes and manually schedules all the jobs on the different computing nodes.


CondorBackend (unstable)
--------------------------
The [CondorBackend](@ref benchmax::CondorBackend) is aimed at the HTCondor batch system and works similar to the SlurmBackend. Note however that this backend is not well tested and we therefore consider it unstable.