#!/bin/bash
echo "" > testrun_wrongresults.log
for f in ~/Dokumente/InformatikStudium/Doktorarbeit/reals_diss/software/benchmarks/sets/smtlib/qf_nra/bugs/wrong_results/*; do echo -ne "Checking $f..." >> testrun_wrongresults.log && ./smtratSolver $f >> testrun_wrongresults.log 2>>testrun_wrongresults.log && mv -v assumptions_to_check.smt2 certification_$(basename $f).smt2 >>testrun_wrongresults.log; done

