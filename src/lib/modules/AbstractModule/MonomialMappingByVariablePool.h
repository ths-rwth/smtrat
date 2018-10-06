
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
        std::unordered_map<carl::Variable, carl::Monomial::Arg> mMonomialMapping;
    public:
        const std::unordered_map<carl::Variable, carl::Monomial::Arg> &getMMonomialMapping() const {
            return mMonomialMapping;
        }

    private:
        carl::Variable nullVariable = carl::freshRealVariable("0");

    public:
        void insertMonomialMapping(carl::Variable variable, carl::Monomial::Arg monomial) {
            mMonomialMapping[variable] = monomial;
        }

        carl::Variable variable(carl::Monomial::Arg monomial) {

            std::unordered_map<carl::Variable, carl::Monomial::Arg>::iterator it;

            for (it = mMonomialMapping.begin(); it != mMonomialMapping.end(); ++it) {
                if (it->second == monomial)
                    return it->first;
            }

            return nullVariable;
        }

        bool isNull(carl::Variable variable){
            return variable == nullVariable;
        }

       carl::Monomial::Arg monomial(carl::Variable variable) {

           std::unordered_map<carl::Variable, carl::Monomial::Arg>::iterator it;

           it = mMonomialMapping.find(variable);
           carl::Monomial::Arg monomial = it->second;

           if (it != mMonomialMapping.end()) {
               carl::Monomial::Arg monomial = it->second;
               return monomial;
           }

           return nullptr;
        }
    };

}