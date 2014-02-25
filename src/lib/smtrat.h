/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


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

#ifndef SMTRAT_H
#define SMTRAT_H

#include "Constraint.h"
#include "ConstraintPool.h"
#include "Manager.h"
#include "modules/AddModules.h"
#include "strategies/strategies.h"
#include "Module.h"
#include "ModuleFactory.h"

#endif   /** SMTRAT_H */





