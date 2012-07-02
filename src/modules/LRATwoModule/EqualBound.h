/*
 * EqualBound.h
 *
 *  Created on: May 11, 2012
 *      Author: cornflake
 */

#ifndef EQUALBOUND_H_
#define EQUALBOUND_H_

#include "Bound.h"

namespace smtrat {

class EqualBound : public Bound {
public:
	EqualBound();
	EqualBound(Real bound);
	virtual ~EqualBound();

	string toString();
	bool checkBound(Real alpha, Real beta);
};

} /* namespace smtrat */
#endif /* EQUALBOUND_H_ */
