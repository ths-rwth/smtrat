/**
 * Class to create the formulas for axioms.
 * @author Aklima Zaman
 * @since 2018-09-24
 * @version 2018-09-24
 */

#pragma once


#include "lib/Common.h"
#include "Util.h"


namespace smtrat {

    class AxiomFactory {

    public:
        enum AxiomType { ZERO, TANGENT_PLANE };

        static FormulasT createFormula(AxiomType axiomType, MonomialMap monomialMap);
    };

}