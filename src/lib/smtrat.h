/**
 *
 * @file smtrat.h
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @author Florian Corzilius
 * @since 2012-01-19
 * @version 2012-07-07
 */

/** @mainpage
 * SMT-RAT is a toolbox which is specifically tailored to be used by an SMT solver in order to solve non-linear real arithmetic (NRA) efficiently.  NRA is an important but hard-to-solve theory and
 * only a fragment of it can be handled by some of the currently existing SMT solvers.  The toolbox consists of four modules, implementing the
 * virtual substitution method, the cylindrical algebraic decomposition method, a Groebner bases simplifier and a general simplifier, respectively. The intention of the toolbox is that an SMT-compliant theory solver can be achieved by composing these modules according to a user defined strategy and with the goal to exploit their advantages.
 * Furthermore, it supports the addition of further modules implementing other methods dealing with real arithmetic.
 */

#pragma once


#include "config.h"
#include "strategies/strategies.h"
#include "modules/AddModules.h"
#include "utilities/SettingsManager.h"





