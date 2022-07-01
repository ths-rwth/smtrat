
#pragma once

#include <carl-common/memory/Singleton.h>
#include <string>
#include "Util.h"

namespace smtrat{

    class MonomialMappingByVariablePool : public carl::Singleton<MonomialMappingByVariablePool>{
        friend class carl::Singleton<MonomialMappingByVariablePool>;

    private:
        // Members:
        MonomialMap mMonomialMapping;
    public:
        const MonomialMap &getMMonomialMapping() const {
            return mMonomialMapping;
        }

    private:
        carl::Variable nullVariable = carl::fresh_real_variable("0");

    public:
        void insertMonomialMapping(carl::Variable variable, carl::Monomial::Arg monomial) {
            mMonomialMapping[variable] = monomial;
        }

        carl::Variable variable(carl::Monomial::Arg monomial) {

            MonomialMapIterator it;

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

           MonomialMapIterator it;

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