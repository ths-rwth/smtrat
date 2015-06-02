/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * @file EQPreprocessingStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-12-05
 * Created on 2014-12-05.
 */


#pragma once

#include "../../config.h"
#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat {
	class EQPreprocessingStatistics : public Statistics {
		private:
			// Members.
			/**
			 * Number of congruences explicitly added to the formula during UF => EQ rewriting.
			 */
			size_t mCongruencesAdded;

		public:
			// Override Statistics::collect.
			void collect() {
				Statistics::addKeyValuePair("congruences_added", mCongruencesAdded);
			}

			void countCongruencesAdded(std::size_t congruences) {
				mCongruencesAdded += congruences;
			}

			EQPreprocessingStatistics() :
				Statistics("EQPreprocessingModule", this),
				mCongruencesAdded(0)
			{}

			~EQPreprocessingStatistics() {}
	};
}

#endif
