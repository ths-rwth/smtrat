/*
 * BetaMap.h
 *
 *  Created on: Apr 23, 2012
 *      Author: NewMoon
 */

#ifndef BETAMAP_H_
#define BETAMAP_H_
#include <ginac/ginac.h>
//#include "SimplexTableaux.h"
#include "Real.h"
using GiNaC::ex;

namespace smtrat
{
    class BetaMap:
        public std::map<const ex, Real>
        {
        public:
        	BetaMap();
//        	BetaMap(GiNaC::ex var, Real beta);
        	~BetaMap();

        	Real getBeta(const ex var) const;
        	void setBeta( ex var, Real beta );
//        	void updateBeta( SimplexTableaux tab, ex basic, ex nonbasic, Real value );
//        	void upateBeta2( SimplexTableaux tab, ex nonbasic, Real candidate);

        	string toString();
        private:

        };

}




#endif /* BETAMAP_H_ */
