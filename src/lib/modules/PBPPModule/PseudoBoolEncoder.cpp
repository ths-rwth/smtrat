#include "PseudoBoolEncoder.h"

namespace smtrat {

        FormulaT PseudoBoolEncoder::generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type) {
            FormulasT newSubformulas;
            for(const auto& var: vars){
                FormulaT newFormula = FormulaT(var);
                newSubformulas.push_back(newFormula);
            }
            return FormulaT(type, std::move(newSubformulas));
        }
}
