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


#ifndef GENERALSTATISTICS_H
#define	GENERALSTATISTICS_H

#include "../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../Formula.h"
#include "../utilities/stats/Statistics.h"

namespace smtrat
{
    class GeneralStatistics : public Statistics
    {
       public:
         // Override Statistics::collect.
         void collect()
         {
            Statistics::addKeyValuePair( "boolean_variables", variablePool().numberOfBooleanVariables() );
            Statistics::addKeyValuePair( "real_variables", variablePool().numberOfRealVariables() );
            Statistics::addKeyValuePair( "integer_variables", variablePool().numberOfIntVariables() );
            Statistics::addKeyValuePair( "constraints", constraintPool().size() );
            Statistics::addKeyValuePair( "non-linear_constraints", constraintPool().nrNonLinearConstraints() );
            Statistics::addKeyValuePair( "maximal_degree", constraintPool().maxDegree() );
         }

        GeneralStatistics() : Statistics("General", this)
        {}
    };
}

#endif
#endif	/* GENERALSTATISTICS_H */