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
 * @file Modules.h
 *
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since 2012-01-18
 * @version 2012-02-04
 */

#ifndef SMTRAT_MODULES_H
#define SMTRAT_MODULES_H

#include "VSModule.h"
#include "SmartSimplifier.h"
#include "FourierMotzkinSimplifier.h"

#ifdef USE_GB
#include "GroebnerModule.h"
#endif

#ifdef USE_CAD
#include "UnivariateCADModule.h"
#include "CADModule.h"
#endif

#include "SATModule.h"
#include "LRAModule.h"
#include "LRAOneModule.h"
#include "LRATwoModule.h"
#include "PreProModule.h"
#include "CNFerModule.h"
#include "SingleVSModule.h"

#include "StandardModuleFactory.h"

#endif   // SMTRAT_MODULES_H

