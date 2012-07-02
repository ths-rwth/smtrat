/*
 * EqualBound.cpp
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */
#include "EqualBound.h"
using namespace std;

namespace smtrat {

	EqualBound::EqualBound() {
		this->deactivate();
	}

	EqualBound::EqualBound(Real bound) {
		this->setBound(bound);
		this->deactivate();
	}

	EqualBound::~EqualBound() {}

	string EqualBound::toString() {
		string result = "EqualBound(";
		result += this->getBound().toString();
		result += ") is ";
		if (this->isActive()) {
			result += "activated!";
		} else {
			result += "not active!";
		}
		return result;
	}

	// not to be de/in - creased
	bool EqualBound::checkBound(Real alpha, Real beta) {
		return false;
	}


} /* namespace smtrat */
