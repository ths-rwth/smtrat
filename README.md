# SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox

## Levelwise construction of a single cylindrical algebraic cell

**Contact**

    Jasper Nalbach <nalbach@cs.rwth-aachen.de>

## Instructions

* Install the CArL version from https://github.com/ths-rwth/carl/tree/pub/onecell following the instructions in the [CArL documentation](http://smtrat.github.io/carl)
* Set up SMT-RAT following the instructions from [SMT-RAT documentation](http://smtrat.github.io/)
* Set the according strategy

## Strategies

Solver | Stragegy
---|---
NL | MCSATNL
OC-ASC | MCSATOCNNASC
OC-DSC | MCSATOCNNDSC
LW-EQ-BC | MCSATOCLWH11
LW-EQ-CH | MCSATOCLWH12
LW-EQ-LDB | MCSATOCLWH13
LW-CH-CH | MCSATOCLWH22
LW-LDB-LDB | MCSATOCLWH33
NL+ | MCSATFMICPVSNL
OC-ASC+ | MCSATFMICPVSOCNNASC
LW-EQ-BC+ | MCSATFMICPVSOCLWH11
LW-EQ-CH+ | MCSATFMICPVSOCLWH12
LW-EQ-LDB+ | MCSATFMICPVSOCLWH13

## Documentation

For more information, please checkout the docs.

* [SMT-RAT documentation](http://smtrat.github.io/)
* [CArL documentation](http://smtrat.github.io/carl) (SMT-RAT depends on [CArL](https://github.com/smtrat/carl) for formula and polynomial data structures and basic operations)
