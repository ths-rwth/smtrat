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
 * @file   MonomialIterator.h
 * @author Sebastian Junges
 *
 * @version 2012-04-10
 */

#ifndef MONOMIALITERATOR_H
#define	MONOMIALITERATOR_H

#include "definitions.h"

namespace smtrat {
	class MonomialIterator {
	public:
		MonomialIterator(unsigned nrVars, unsigned maxDeg = 5);
		virtual ~MonomialIterator();
		Term next();
		bool hasNext() { return !mTerms.empty() || mCurDeg < mMaxDeg; }
		
		void test(unsigned deg);
	private:
		void fillExps(unsigned firstVar, unsigned degLeft);
		
		std::vector<unsigned> mExps;
		std::list<std::vector<unsigned> > mTerms;
		unsigned mNrVars;
		unsigned mMaxDeg;
		unsigned mCurDeg;
	
	};
}

#endif	/* MONOMIALITERATOR_H */

