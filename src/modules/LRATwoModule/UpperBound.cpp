/*
 * UpperBound.cpp
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */

#include "UpperBound.h"
using namespace std;

namespace smtrat {

	UpperBound::UpperBound() {
		this->deactivate();
	}

	UpperBound::UpperBound(Real bound) {
		this->setBound(bound);
		this->deactivate();
	}

	UpperBound::~UpperBound() {}

	string UpperBound::toString() {
		string result = "UpperBound(";
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
	bool UpperBound::checkBound(Real alpha, Real beta) {
			return (this->getBound()) >= (beta - alpha);
	}

} /* namespace smtrat */
