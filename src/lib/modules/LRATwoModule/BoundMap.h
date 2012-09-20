/*
 * BoundMap.h
 *
 *  Created on: Apr 24, 2012
 *      Author: cornflake
 */

#ifndef BOUNDMAP_H_
#define BOUNDMAP_H_

#include "Bound.h"
#include "LowerBound.h"
#include "UpperBound.h"
#include "EqualBound.h"
#include "../../Constraint.h"
#include <sstream>

using std::map;
using std::vector;
using std::pair;
using std::cout;
using GiNaC::ex;
using GiNaC::numeric;

namespace smtrat
{
    struct constraintCmp
    {
        bool operator ()( const smtrat::Constraint* const pConstraintA, const smtrat::Constraint* const pConstraintB ) const
        {
            bool sameRelation        = pConstraintA->relation() == pConstraintB->relation();
            bool sameLhs             = pConstraintA->lhs().is_equal( pConstraintB->lhs() );
            bool differentConstraint = !sameRelation ||!sameLhs;
            return differentConstraint;
        }
    };

    class BoundMap:
        public map<const Constraint*, Bound*, constraintCmp>
    {
        public:

            BoundMap();
            virtual ~BoundMap();
            void addBound( const ex variable, const Constraint* constraint, numeric coefficient, numeric constant, Constraint_Relation relation );
            string toString();

            map<const Constraint*, const ex, constraintCmp> getConstraintToVarMap()
            {
                return this->constraintToVarMap;
            }

            string constraintToVarMapAsString();

            map<const ex, const Constraint*> getVarToConstraintMap()
            {
                return this->varToConstraintMap;
            }

            string varToConstraintMapAsString();

            vector<pair<const Constraint*, Bound*> > getActives()
            {
                return this->actives;
            }

            //bool assertUpper(const ex variable, Real upperCandidate, BetaMap *betaMap, SimplexTableaux *tab);
            //bool assertLower(const ex variable, Real lowerCandidate, BetaMap *betaMap, SimplexTableaux *tab);

        private:
            typedef map<const Constraint*, const ex, constraintCmp> ConstraintToVarMap;
            ConstraintToVarMap                                      constraintToVarMap;
            typedef map<const ex, const Constraint*>                VarToConstraintMap;
            VarToConstraintMap                                      varToConstraintMap;

            typedef vector<pair<const Constraint*, Bound*> >        Actives;
            Actives                                                 actives;
    };

}

#endif /* BOUNDMAP_H_ */
