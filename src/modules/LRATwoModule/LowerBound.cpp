/*
 * LowerBound.cpp
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */

#include "LowerBound.h"
using namespace std;

namespace smtrat {

	LowerBound::LowerBound() {
		this->deactivate();
	}

	LowerBound::LowerBound(Real bound) {
		this->setBound(bound);
		this->deactivate();
	}

	LowerBound::~LowerBound() {}

	string LowerBound::toString() {
		string result = "LowerBound(";
		result += this->getBound().toString();
		result += ") is ";
		if (this->isActive()) {
			result += "activated!";
		} else {
			result += "not active!";
		}
		return result;
	}

	// alpha is the value with which we must increase/decrease
	bool LowerBound::checkBound(Real alpha, Real beta) {
			return (this->getBound()) <= (beta + alpha);
	}

} /* namespace smtrat */
