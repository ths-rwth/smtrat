#!/bin/bash
STATISTICS_A=":decisions"
STATISTICS_B=":decisions"
OPTIONS_A=" -s "
OPTIONS_B=" -st "
res1=`smtrat $1`
exitvalue=$?
res1=`smtrat $OPTIONS_A $1 2>&1 | grep "$STATISTICS_A" | sed 's/[^0-9]//g'`
if [[ $res1 -eq "" ]]; then
    exit 0
fi
res2=`z3 $OPTIONS_B $1 2>&1 | grep "$STATISTICS_B" | sed 's/[^0-9]//g'`
if [[ $res2 -eq "" ]]; then
    exit 0
fi
res3=$res2+1
if [[ $res2 -gt 0 && $res1 -gt 250*$res3 && $exitvalue -eq 2 ]]; then
    exit 123
else
    exit 0
fi
