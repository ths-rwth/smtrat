#!/bin/bash
OUTPUTFILE=$1
SOLVER=$2
LOGFILE="$OUTPUTFILE.log"
echo -ne "Recording certifications from $SOLVER in certification\_$OUTPUTFILE\_*.smt2."
echo "" > $LOGFILE
for f in ~/Dokumente/InformatikStudium/Doktorarbeit/reals_diss/software/benchmarks/sets/smtlib/qf_nra/bugs/wrong_results/*; do echo -ne "Checking $f..." >> $LOGFILE && ./smtratSolver $f >> $LOGFILE 2>>$LOGFILE && mv -v assumptions_to_check.smt2 certification\_$OUTPUTFILE\_$(basename $f) >>$LOGFILE; done

