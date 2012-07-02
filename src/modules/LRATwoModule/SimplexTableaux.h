/*
 * SimplexTableaux.h
 *
 *  Created on: Apr 30, 2012
 *      Author: cornflake
 */

#ifndef SIMPLEXTABLEAUX_H_
#define SIMPLEXTABLEAUX_H_

#include <ginac/ginac.h>
#include <sstream>
#include "../../Constraint.h"
#include "BoundMap.h"
#include "BetaMap.h"
using std::string;
using std::map;
using std::pair;
using GiNaC::ex;
using std::vector;
using GiNaC::numeric;
using GiNaC::ex_is_less;

namespace smtrat
{
	class SimplexTableaux: public map<int, map<int, numeric> >  {
	public:
		SimplexTableaux();
		virtual ~SimplexTableaux();

		pair<bool, numeric> getEntry(const ex row, const ex column) const;
		pair<bool, numeric> getEntry(int row, int column) const;
		void setEntry(int row, int column, numeric value);
		void setEntry(const ex row, const ex column, numeric value);

		// divide every entry by coefficient at position (row,column) times -1
		void updateRow(int row, int column);
		void updateRow(const ex row, const ex column);

		map<const Constraint*, const ex> getNonBasicsAsConstraints(BoundMap* boundMap) const;

        // writes output
        void output_writing(int column, int row, string upd_obj);

        void pivotAndUpdate(const ex basic, const ex nonbasic, const Real* value, BetaMap* assignment);

		bool inform(const Constraint* const constraint, BoundMap *boundMap);

		map<const ex, int> getBasics();
		map<const ex, int> getNonBasics();

		bool assertStrictUpper(const Constraint* const _constraintNew, const Constraint* const _constraintOld, Bound* newBound,
						Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap);
		bool assertStrictLower(const Constraint* const _constraintNew, const Constraint* const _constraintOld, Bound* newBound,
						Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap);
		bool assertUpper(const Constraint* const _constraintNew, const Constraint* const _constraintOld, Bound* newBound,
						Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap);
		bool assertLower(const Constraint* const _constraintNew, const Constraint* const _constraintOld, Bound* newBound,
						Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap);

		string toString() ;

	private:
		typedef map<const ex, int> LocationMap;
		//	basic the rows of the tableaux
		LocationMap basicVariablesLocation;
		//	nonbasic the columns of the tableaux
		LocationMap nonBasicVariablesLocation;

		int newVariableCount;
		int columnCount;

		void inform(const Constraint* const constraint, GiNaC::symtab variables, vector<ex> coefficients, BoundMap *boundMap);
	};
}
#endif /* SIMPLEXTABLEAUX_H_ */
