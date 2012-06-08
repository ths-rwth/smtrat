/*
 * BoundMap.cpp
 *
 *  Created on: May 8, 2012
 *      Author: cornflake
 */

#include "BoundMap.h"
using namespace std;
using namespace GiNaC;

namespace smtrat
{
	BoundMap::BoundMap()
			: map()
			, constraintToVarMap()
			, varToConstraintMap()
			, actives() {}

	BoundMap::~BoundMap() {}

	// called eg if a new constraint is added and thus, new bounds might be asserted
	// TODO replace ex variable bei constraint?!
	// TODO write isEqual method for constraints in that case + add fresh constraint -infty � x � infty for each original var x
//	bool BoundMap::assertUpper(const ex variable, Real upperCandidate, BetaMap *betaMap, SimplexTableaux *tab) {
//		 //satisfiable
//		if (upperCandidate >= variable.bound.getUpper()){
//			return true;
//		}
//		if (upperCandidate < variable.bound.getLower()){
//					return false;
//		}
//		variable.bound.setUpper(upperCandidate);
//		map<ex, int>::iterator it = tab->getNonBasics().find(variable);
//		if(it != tab->getNonBasics.end() && betaMap->getBeta(variable) < upperCandidate) {
//			betaMap->udateBeta2(tab, variable, upperCandidate);
//		}
//		return true;
//	}
//
//	bool BoundMap::assertLower(const ex variable, Real lowerCandidate, BetaMap *betaMap, SimplexTableaux *tab){
//
//	 //satisfiable
//		if (lowerCandidate <= variable.bound.getLower()){
//			return true;
//		}
//		if (lowerCandidate > variable.bound.getUpper()){
//			return false;
//		}
//		variable.bound.setLower(lowerCandidate);
//		map<ex, int>::iterator it = tab->getNonBasics().find(variable);
//		if(it != tab->getNonBasics().end() && betaMap->getBeta(variable) < lowerCandidate) {
//			betaMap->upateBeta2(tab, variable, lowerCandidate);
//		}
//		return true;
//	}

	string BoundMap::toString() {
		string result = "BoundMap:\n";
		int maxLength = 0;
		int length = 0;
		for (map<const Constraint*, Bound*>::const_iterator iterator=this->begin(); iterator != this->end(); ++iterator) {
			length = iterator->first->toString().length();
			if (length > maxLength ) {
				maxLength = length;
			}
		}
		for (map<const Constraint*, Bound*>::const_iterator pair=this->begin(); pair!= this->end(); ++pair) {
			result += "Entry:\t";
			const Constraint* cons = pair->first;
			result += cons->toString();
			length = pair->first->toString().length();
			for (; length < (maxLength + 3); ++length) {
				result += " ";
			}
			result += " -> ";
			ostringstream osstream;
			osstream << cons;
			osstream << " -> ";
			Bound* bound = pair->second;
			for (map<const Constraint*, const ex>::const_iterator it=this->constraintToVarMap.begin(); it != this->constraintToVarMap.end(); ++it) {
				const Constraint* first = it->first;
				if ((first->relation() == cons->relation()) && (first->lhs().is_equal(cons->lhs()))){
					const ex var = it->second;
					osstream << var;
					break;
				}
			}
//			cout << "\n" << "searching for constraint: " << pair->first->toString() << "\n" << this->constraintToVarMapAsString() << "\n";
//			const ex* var = this->constraintToVarMap.at(pair->first);
//			osstream << *var;
			osstream << " \t -> ";
			result += osstream.str();
			result += bound->toString();
			result += "\n";
		}
		return result;
	}

	string BoundMap::constraintToVarMapAsString() {
		string result = "ConstraintToVarMap:\n";
		for (map<const Constraint*, const ex>::const_iterator iterator=this->constraintToVarMap.begin(); iterator != this->constraintToVarMap.end(); ++iterator) {
			result += iterator->first->toString();
			result += " -> ";
			ostringstream osstream;
			osstream << (iterator->second);
			result += osstream.str();
			result += "\n";
		}
		result += "\n";
		return result;
	}

	string BoundMap::varToConstraintMapAsString() {
		string result = "VarToConstraintMap:\n";
		for (map<const ex, const Constraint*>::const_iterator iterator=this->varToConstraintMap.begin(); iterator != this->varToConstraintMap.end(); ++iterator) {
			ostringstream osstream;
			osstream << (iterator->first);
			result += osstream.str();
			result += " -> ";
			result += iterator->second->toString();
			result += "\n";
		}
		result += "\n";
		return result;
	}

	void BoundMap::addBound(const ex variable, const Constraint* constraint, numeric coefficient, numeric constant, Constraint_Relation relation) {
			/**
			 * we get a variable, a coefficient, a numeric and a relation which initially looked like:
			 * coefficient * variable + constant relation 0
			 * this has to be reformed to:
			 * coefficient relation -constant/coefficient
			 */
			numeric rhs = -constant/coefficient;
			switch( relation)
			{
			case CR_EQ: // =
			{
				EqualBound* bound = new EqualBound(Real(rhs, false));
				this->insert(pair<const Constraint*, EqualBound*>(constraint, bound));
				this->constraintToVarMap.insert(pair<const Constraint*, const ex>(constraint, variable));
				this->varToConstraintMap.insert(pair<const ex, const Constraint*>(variable, constraint));
				break;
			}
			case CR_NEQ: // <>
			{
				// should never get here.... I think
				// assert(false); // have to deactivate this if debugging with examples using <>
				break;
			}
			case CR_LESS: // <
			{
				UpperBound* bound = new UpperBound(Real(rhs, true));
				this->insert(pair<const Constraint*, UpperBound*>(constraint, bound));
				this->constraintToVarMap.insert(pair<const Constraint*, const ex>(constraint, variable));
				this->varToConstraintMap.insert(pair<const ex, const Constraint*>(variable, constraint));
				break;
			}
			case CR_GREATER: // >
			{
				LowerBound* bound = new LowerBound(Real(rhs, true));
				this->insert(pair<const Constraint*, LowerBound*>(constraint, bound));
				this->constraintToVarMap.insert(pair<const Constraint*, const ex>(constraint, variable));
				this->varToConstraintMap.insert(pair<const ex, const Constraint*>(variable, constraint));
				break;
			}
			case CR_LEQ: // <=
			{
				UpperBound* bound = new UpperBound(Real(rhs, false));
				this->insert(pair<const Constraint*, UpperBound*>(constraint, bound));
				this->constraintToVarMap.insert(pair<const Constraint*, const ex>(constraint, variable));
				this->varToConstraintMap.insert(pair<const ex, const Constraint*>(variable, constraint));
				break;
			}
			case CR_GEQ: // >=
			{
				LowerBound* bound = new LowerBound(Real(rhs, false));
				this->insert(pair<const Constraint*, LowerBound*>(constraint, bound));
				this->constraintToVarMap.insert(pair<const Constraint*, const ex>(constraint, variable));
				this->varToConstraintMap.insert(pair<const ex, const Constraint*>(variable, constraint));
				break;
			}
			default:
			{
				break;
			}
			}
		}

}
