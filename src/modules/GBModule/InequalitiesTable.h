/* 
 * File:   InequalitiesTable.h
 * Author: square
 *
 * Created on June 18, 2012, 2:41 PM
 */

#include "GBSettings.h"

#ifndef INEQUALITIESTABLE_H
#define	INEQUALITIESTABLE_H

namespace smtrat {
		
		
	class InequalitiesRow {
		typedef GBSettings::Polynomial Polynomial;
		typedef GBSettings::MultivariateIdeal Ideal;
	public:
		InequalitiesRow(const Formula* const received, unsigned btpoint) :
		receivedFormulaEntry(received), relation(received->constraint().relation())
		{
			reductions.push_back(std::pair<unsigned, Polynomial>(btpoint, Polynomial(received->constraint().lhs()) ) );
		}
		
		void ReduceWithGb(const Ideal& gb) {
			
		}
	protected:
		const Formula* receivedFormulaEntry;
		Constraint_Relation relation;
		Formula* passedFormulaEntry;
		std::list<std::pair<unsigned,Polynomial> > reductions;
	};
	
	
	class InequalitiesTable {
		
		typedef GBSettings::Polynomial Polynomial;
		typedef GBSettings::MultivariateIdeal Ideal;
	public: 
		void InsertReceivedFormula(const Formula* const received ) {
			mReducedInequalities.push_back(InequalitiesRow(received, mNrInequalitiesForBtPoints.size() ) );
		}
		
		void PushBacktrackPoint() {
			
		}
		
		void PopBacktrackPoint() {
			
		}
		
		void ReduceWRTGroebnerBasis(const Ideal& gb) {
			for(std::vector<InequalitiesRow>::iterator it = mReducedInequalities.begin(); it != mReducedInequalities.end(); ++it) {
				
			}
		}
		
		std::list<size_t> mNrInequalitiesForBtPoints;
		std::vector<InequalitiesRow> mReducedInequalities;
		
		
	};
}


#endif	/* INEQUALITIESTABLE_H */

