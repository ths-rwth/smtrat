#!/bin/bash
# remove the status flag from the .smt2 file, otherwise, this script won't work
SAT="sat"
UNSAT="unsat"
OPTIONS=""
res1=`smtrat $OPTIONS $1`
res2=`z3 $1`
if [[ $res1 == $SAT && $res2 == $UNSAT ]]; then
    exit 1
fi
if [[ $res1 == $UNSAT && $res2 == $SAT ]]; then
    exit 1
fi
exit 0