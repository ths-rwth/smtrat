# Benchmax {#mainpage}

Benchmax is a tool for automated benchmarking.
Though it was developed and is primary used for testing SMT solvers, it aims to be agnostic of the tools and formats as good as possible.

Its fundamental model is to load a list of tools and a list of benchmarks, run every tool with every benchmark, obtain the results and output all the results. While the benchmarks are fixed to a single file, we allow to choose between different [tool interfaces](@ref tools), [execution backends](@ref backends) and output formats.

