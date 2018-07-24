
#pragma once

#include "carl/util/Singleton.h"
#include "carl/core/Monomial.h"
#include "unordered_map"
#include <string>

namespace smtrat{

    class MonomialMappingByVariablePool : public carl::Singleton<MonomialMappingByVariablePool>{
        friend class carl::Singleton<MonomialMappingByVariablePool>;

    private:
        // Members:
        std::unordered_map<carl::Variable, Poly> mMonomialMapping;
    public:
        void InsertMonomialMapping(carl::Variable variable, std::shared_ptr<const carl::Monomial>& mMonomial) {
            carl::MultivariatePolynomial<Rational> p(mMonomial);
            mMonomialMapping[variable] = p;
        }

        carl::Monomial::Arg Monomial(carl::Variable variable) {

            std::unordered_map<carl::Variable, Poly>::iterator it;
            it = mMonomialMapping.find(variable);
            if (it != mMonomialMapping.end()) {
                Poly p = it->second;
                for( auto& term : p.getTerms() ) {
                    if( !term.isConstant() ) {
                        return term.monomial();
                    }
                }
            }
            return nullptr;
        }
    };

}