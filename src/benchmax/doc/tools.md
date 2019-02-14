Tools {#tools}
==============

A tool represents a binary that can be executed on some input files.
It is responsible for deciding whether it can be applied to some given file, building a command line to execute it and retrieve additional results from stdout or stderr.

The generic tool class benchmax::Tool can be used as a default.
It will run the given binary on any input file and benchmax records the exit code as well as the runtime.

If more information is needed a new tool class can be derived that overrides or extends the default behaviour. Some premade tools are available (and new ones should be easy to create):

- benchmax::Minisatp
- benchmax::SMTRAT
- benchmax::SMTRAT_OPB
- benchmax::Z3