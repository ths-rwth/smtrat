#!/bin/bash
for f in certification_*.smt2; do echo "Verifying $f..." && (z3 $f|grep "error"); done

