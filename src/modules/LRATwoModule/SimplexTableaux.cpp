/*
 * SimplexTableaux.cpp
 *
 *  Created on: Apr 30, 2012
 *      Author: cornflake
 *  Updates on: May 22, 2012
 *      Author: oshults
 *     Changes: updateRow: added check whether element is pivoting
 *              pivot method
 *  Updates on: June 5, 2012
 *     Changes: PivotAndUpdate
 */

#include "SimplexTableaux.h"
using namespace std;
using namespace GiNaC;

namespace smtrat {

	SimplexTableaux::SimplexTableaux() :
			map<int, map<int, numeric> >(),
			basicVariablesLocation(),
			nonBasicVariablesLocation(),
			newVariableCount(0),
			columnCount(0) {
	}

	SimplexTableaux::~SimplexTableaux() {
	}

	/**
	 * use this function as a pair.
	 * First of the pair is false, if the entry does not exist in tableaux
	 */
	pair<bool, numeric> SimplexTableaux::getEntry(int row, int column) const {
		numeric result;
		bool existing = true;
		map<int, numeric> rowMap;
		try { // to find the row, if not exists return false
			rowMap = this->at(row);
			result = rowMap.at(column);
		} catch (exception &e) {
			existing = false;
			result = 0;
		};
		return pair<bool, numeric>(existing, result);
	}

	/**
	 * use this function as a pair.
	 * First of the pair is false, if the entry does not exist in tableaux
	 */
	pair<bool, numeric> SimplexTableaux::getEntry(const ex row, const ex column) const {
		int rowOfVariable = this->basicVariablesLocation.at(row);
		int columnOfVariable = this->nonBasicVariablesLocation.at(column);
		return getEntry(rowOfVariable, columnOfVariable);
	}

	void SimplexTableaux::setEntry(int row, int column, numeric value) {
		map<int, numeric> rowMap;
		try { // to find the row, if not exists create one
			this->at(row);
		} catch (...) {
			map<int, numeric> newRow = map<int, numeric>();
			this->insert(pair<int, map<int, numeric>>(row, newRow));
		};
		this->at(row).insert(pair<int, numeric>(column, value));
	}

	void SimplexTableaux::setEntry(const ex row, const ex column, numeric value) {
		int rowOfVariable = this->basicVariablesLocation.at(row);
		int columnOfVariable = this->nonBasicVariablesLocation.at(column);
		setEntry(rowOfVariable, columnOfVariable, value);
	}

	map<const ex, int> SimplexTableaux::getBasics() {
		return this->basicVariablesLocation;
	}

	map<const ex, int> SimplexTableaux::getNonBasics() {
		return this->nonBasicVariablesLocation;
	}

	map<const Constraint*, const ex> SimplexTableaux::getNonBasicsAsConstraints(
			BoundMap* boundMap) const {
		map<const Constraint*, const ex> setOfConstraints;
		map<const ex, const Constraint*> varToConstMap =
				boundMap->getVarToConstraintMap();
		map<const ex, const Constraint*>::const_iterator itConst;
		map<const ex, int>::const_iterator itEx;

		for (itEx = this->nonBasicVariablesLocation.begin();
				itEx != this->nonBasicVariablesLocation.end(); ++itEx) {
			itConst = varToConstMap.find(itEx->first);
			if (itConst != varToConstMap.end()) {
				setOfConstraints.insert(
						pair<const Constraint*, const ex>(itConst->second,
								itConst->first));
			} else {
				cout
						<< "Could not find corresponding Constraint to ex "
								"in method vector<const Constraint*> SimplexTableaux::getNonBasicsAsConstraints(BoundMap* boundMap) const; !!!";
			}

		}
		return setOfConstraints;
	}



	void SimplexTableaux::updateRow(const ex row, const ex column) {
		int rowOfVariable = this->basicVariablesLocation.at(row);
		int columnOfVariable = this->nonBasicVariablesLocation.at(column);
		updateRow(rowOfVariable, columnOfVariable);
	}

	// divide every entry by coefficient at position (row,column) times -1

	void SimplexTableaux::updateRow(int row, int column) {
		map<int, numeric> mapOfRow = this->at(row);
		numeric divisor = mapOfRow[column];
		for (map<int, numeric>::iterator iter = mapOfRow.begin();
				iter != mapOfRow.end(); ++iter) {
			//all the coefficients of row except current is divided by divisor
			if (iter->first != column) {
				iter->second = -((iter->second) / divisor);
			}
			//coefficient of pivoting column and row is:
			else {
				iter->second = (1 / divisor);
			}
		}
	}

        void SimplexTableaux::output_writing(int column, int row, string upd_obj){
                string output;
                ostringstream stream1;
                ostringstream stream2;
                stream1 << column;
                output += stream1.str();
		output += ", ";
                stream2 << row;
		output += stream2.str();
		cout
		<< upd_obj << output << ") in the current Simplex Tableaux. \n Abort. \n";
        }

        void SimplexTableaux::pivotAndUpdate(const ex basic, const ex nonbasic,
        		const Real* value, BetaMap* assignment) {
        	int row = this->basicVariablesLocation.at(basic);
        	int column = this->nonBasicVariablesLocation.at(nonbasic);
        	map<int, numeric> mapOfRow;
        	bool rowExisting = true;
        	bool columnExisting = true;
        	bool currentCoefExisting = true;
        	bool currentPivotCoefExisting = true;
        	numeric columnValue;
        	map<int, numeric> iter_row;
        	numeric coeff;
        	numeric pivot_coeff;
        	string upd_obj_pivot = "Tableaux pivot is not possible! \n There exists no coefficient for the pair (column, row) = (";
        	bool nonbasicExisting = true;
        	bool basicExisting = true;
        	Real nonbasicBeta;
        	Real basicBeta;
        	Real updateVal;
        	Real currBasicBeta;
        	bool currBasicVarExisting=true;
        	string upd_obj_beta = "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (";

        	// do this with every map.at() call if you are not sure (100%) that the entry exists.
        	// we have to test if the entry exists, if not there is an exception that is thrown!
        	try {
        		mapOfRow = this->at(row);
        	} catch (...) {
        		rowExisting = false;
        	};
        	try {
        		columnValue = mapOfRow.at(column);
        	} catch (...) {
        		columnExisting = false;
        	};

        	// check whether the entry exists
        	// get the basic variable's current beta value needed to compute updateVal (see below)
        	try {
        		basicBeta = assignment->at(basic);
        	}
        	catch ( ... ) {
        		basicExisting = false;
        	};
        	try {
        		nonbasicBeta = assignment->at(nonbasic);
        	}
        	catch ( ... ) {
        		nonbasicExisting = false;
        	};

        	if (rowExisting && columnExisting && basicExisting && nonbasicExisting) {
        		//update row, where pivoting elements are
        		updateRow(row, column);
        		//already updated row
        		mapOfRow = this->at(row);

        		//update coefficients
        		//iterate over all the rows
        		for (map<int, map<int, numeric> >::iterator i = this->begin(); i != this->end(); ++i) {
        			//change each row except the pivoting one
        			if (i->first != row) {
        				//get the row
        				iter_row = i->second;
        				//get the coefficient of column
        				try {
        					coeff = iter_row.at(column);
        				} catch (...) {
        					currentCoefExisting = false;
        				};

        				if (currentCoefExisting) {
        					//iterate over all columns
        					for (map<int, numeric>::iterator j = iter_row.begin();j != iter_row.end(); ++j) {
        						try {
        							pivot_coeff = mapOfRow.at(j->first);
        						} catch (...) {
        							currentPivotCoefExisting = false;
        						};
        						if (currentPivotCoefExisting) {
        							j->second = coeff * pivot_coeff + (j->second);
        						} else {output_writing(j->first, row, upd_obj_pivot);}
        					}
        				} else {output_writing(column, i->first, upd_obj_pivot);}
        			}
        		}
        		//updateVal is the value with which each beta-value of every var has to be updated
        		updateVal = (*value - basicBeta) / columnValue;

        		//update variables used for pivoting
        		assignment->at(basic) = *value;
        		assignment->at(nonbasic) = assignment->at(nonbasic) + updateVal;

        		//update all remaining basic variables
        		map<const ex, int> basicVars = this->getBasics();
        		basicVars.erase(basic);
        		for (map<const ex, int>::iterator var = basicVars.begin(); var != basicVars.end(); ++var) {
        			const ex row_new = var->first;
        			int row_num = this->basicVariablesLocation.at(row_new);
        			try {
        				currBasicBeta = assignment->at(row_new);
        			}
        			catch ( exception &e ) {
        				currBasicVarExisting = false;
        			};
        			if (currBasicVarExisting){
        				mapOfRow = this-> at(row_num);
        				currBasicBeta = currBasicBeta + mapOfRow.at(column) * updateVal;
        				assignment->at(row_new)= currBasicBeta;
        			}else{output_writing(row_num, column, upd_obj_beta);}
        		}
        	} else {output_writing(column, row, upd_obj_pivot);}
        }

        bool SimplexTableaux::inform(const Constraint * const constraint,
			BoundMap *boundMap) {
		GiNaC::symtab variables = constraint->variables();
		vector<ex> coefficients = constraint->linearAndConstantCoefficients();
		assert( variables.size() > 0);
		if (variables.size() > 1) {
			if (constraint->relation() != CR_NEQ) {
				inform(constraint, variables, coefficients, boundMap);
			}
		} else {
			numeric coefficientOfVar = ex_to<numeric>(coefficients[0]);
			numeric constant = ex_to<numeric>(coefficients[1]);
			ex variable = variables.begin()->second;
			boundMap->addBound(variable, constraint, coefficientOfVar, constant,
					constraint->relation());
		}
		return true;
	}

	void SimplexTableaux::inform(const Constraint * const constraint,
			GiNaC::symtab variables, vector<ex> coefficients, BoundMap *boundMap) {
		int coefficientIndex = 0;
		++newVariableCount;
		string s = "s";
		ostringstream osstream;
		osstream << newVariableCount;
		s += osstream.str();
		symbol newVarSymbol(s);
		const ex newVariable = ex(newVarSymbol);
		// not debugging, use random name later on
		this->basicVariablesLocation.insert(
				pair<const ex, int>(newVariable, newVariableCount));
		for (GiNaC::symtab::const_iterator var = variables.begin();
				var != variables.end(); ++var) {
			map<const ex, int>::iterator it = this->nonBasicVariablesLocation.find(
					var->second);
			int columnOfVariable;
			if (it == this->nonBasicVariablesLocation.end()) {
				//element not found;
				++columnCount;
				// The next command leads to a segmentation fault, apparently the map is not big enought???
				this->nonBasicVariablesLocation.insert(
						pair<const ex, int>(var->second, columnCount));
				columnOfVariable = columnCount;
			} else {
				// element existing, thus determine the column for the variables
				columnOfVariable = this->nonBasicVariablesLocation.at(
						var->second);
			}
			numeric actualCoeff = ex_to<numeric>(coefficients.at(coefficientIndex));
			this->setEntry(newVariableCount, columnOfVariable, actualCoeff);
			++coefficientIndex;
		}
		numeric constant = ex_to<numeric>(coefficients.at(coefficientIndex));
		numeric coefficient = numeric(1);
		boundMap->addBound(newVariable, constraint, coefficient, constant,
				constraint->relation());
	}

	bool SimplexTableaux::assertStrictUpper(const Constraint* const _constraintNew,
			const Constraint* const _constraintOld, Bound* newBound,
			Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap) {
		switch (_constraintOld->relation()) {
		case CR_EQ: // =
		{
			// if the new bound (which is a _strict_upper_ bound on the variable) is smaller or equal to the equal bound of the variable,
			// this is unsatisfiable and no bound tightening is possible
			if (newBound->getBound() <= oldBound->getBound()) {
				return false;
			} else
				return true;
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
			// if the new bound (which is a _strict_upper_ bound on the variable) is smaller or equal to the strict lower bound of the variable,
			// this is unsatisfiable
			if (newBound->getBound() <= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GREATER: // >
		{
			// if the new bound (which is a _strict_upper_ bound on the variable) is greater or equal to the strict upper bound of the variable,
			// this is  directly satisfiable and no bound tightening is possible
			if (newBound->getBound() >= oldBound->getBound()) {
				return true;
			}
			break;
		}
		case CR_LEQ: // <=
		{
			// if the new bound (which is a _strict_upper_ bound on the variable) is smaller or equal to the lower bound of the variable,
			// this is unsatisfiable
			if (newBound->getBound() <= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GEQ: // >=
		{
			// if the new bound (which is a _strict_upper_ bound on the variable) is greater or equal to the upper bound of the variable,
			// this is  directly satisfiable and no bound tightening is possible
			if (newBound->getBound() >= oldBound->getBound()) {
				return true;
			}
			break;
		}
		default: {
			break;
		}
		}
		newBound->activate();
		oldBound->deactivate();
		map<const Constraint*, const ex> nonbasics =
				this->getNonBasicsAsConstraints(boundMap);
		map<const Constraint*, const ex>::const_iterator itConst = nonbasics.find(
				_constraintOld);
		if (itConst != nonbasics.end()) {
			if (betaMap->getBeta(itConst->second) > newBound->getBound()) {
				//TODO updateBeta2(this, itConst->second, newBound->getBound());
				// how can I give a pointer of SimplexTableaux to updateBeta2-method?!
				//do I have to put a pointer on the tableaux when calling assert-methods in LRAModule addConstraint?! seems weird..
			}

		}
		return true;
	}

	bool SimplexTableaux::assertStrictLower(const Constraint* const _constraintNew,
			const Constraint* const _constraintOld, Bound* newBound,
			Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap) {
		switch (_constraintOld->relation()) {
		case CR_EQ: // =
		{
			if (newBound->getBound() >= oldBound->getBound()) {
				return false;
			} else
				return true;
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
			if (newBound->getBound() >= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GREATER: // >
		{
			if (newBound->getBound() <= oldBound->getBound()) {
				return true;
			}
			break;
		}
		case CR_LEQ: // <=
		{
			if (newBound->getBound() >= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GEQ: // >=
		{
			if (newBound->getBound() <= oldBound->getBound()) {
				return true;
			}
			break;
		}
		default: {
			break;
		}
		}
		newBound->activate();
		oldBound->deactivate();
		map<const Constraint*, const ex> nonbasics =
				this->getNonBasicsAsConstraints(boundMap);
		map<const Constraint*, const ex>::const_iterator itConst = nonbasics.find(
				_constraintOld);
		if (itConst != nonbasics.end()) {
			if (betaMap->getBeta(itConst->second) < newBound->getBound()) {
				//TODO updateBeta2(this, itConst->second, newBound->getBound());
				// how can I give a pointer of SimplexTableaux to updateBeta2-method?!
				//do I have to put a pointer on the tableaux when calling assert-methods in LRAModule addConstraint?! seems weird..
			}

		}
		return true;
	}

	bool SimplexTableaux::assertUpper(const Constraint* const _constraintNew,
			const Constraint* const _constraintOld, Bound* newBound,
			Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap) {
		switch (_constraintOld->relation()) {
		case CR_EQ: // =
		{
			if (newBound->getBound() < oldBound->getBound()) {
				return false;
			} else
				return true;
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
			if (newBound->getBound() >= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GREATER: // >
		{
			if (newBound->getBound() <= oldBound->getBound()) {
				return true;
			}
			break;
		}
		case CR_LEQ: // <=
		{
			if (newBound->getBound() >= oldBound->getBound()) {
				return false;
			}
			break;
		}
		case CR_GEQ: // >=
		{
			if (newBound->getBound() <= oldBound->getBound()) {
				return true;
			}
			break;
		}
		default: {
			break;
		}
		}
		newBound->activate();
		oldBound->deactivate();
		map<const Constraint*, const ex> nonbasics =
				this->getNonBasicsAsConstraints(boundMap);
		map<const Constraint*, const ex>::const_iterator itConst = nonbasics.find(
				_constraintOld);
		if (itConst != nonbasics.end()) {
			if (betaMap->getBeta(itConst->second) < newBound->getBound()) {
				//TODO updateBeta2(this, itConst->second, newBound->getBound());
				// how can I give a pointer of SimplexTableaux to updateBeta2-method?!
				//do I have to put a pointer on the tableaux when calling assert-methods in LRAModule addConstraint?! seems weird..
			}

		}

		return true;
	}

	bool SimplexTableaux::assertLower(const Constraint* const _constraintNew,
			const Constraint* const _constraintOld, Bound* newBound,
			Bound* oldBound, BoundMap* boundMap, BetaMap* betaMap) {
		return true;
	}


	string SimplexTableaux::toString() {
		string result = "Simplex Tableaux:\n";
		for (map<const ex, int>::const_iterator rowVar =
				this->basicVariablesLocation.begin();
				rowVar != this->basicVariablesLocation.end(); ++rowVar) {
			result += "The row of: ";
			ostringstream sstream;
			sstream << rowVar->first;
			result += sstream.str();
			result += "\n";
			for (map<const ex, int>::const_iterator columnVar =
					this->nonBasicVariablesLocation.begin();
					columnVar != this->nonBasicVariablesLocation.end();
					++columnVar) {
				const ex rowVarEx = rowVar->first;
				const ex columnVarEx = columnVar->first;
				pair<bool, numeric> entry = this->getEntry(rowVarEx, columnVarEx);
				if (entry.first) {
					result += "The entry of: ";
					ostringstream sstream;
					sstream << columnVar->first << " is: " << entry.second;
					result += sstream.str();
					result += "\n";
				}
			}
			result += "\n";
		}
		return result;
	}

}
