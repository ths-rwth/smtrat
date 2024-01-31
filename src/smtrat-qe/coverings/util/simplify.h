#pragma once

#include "VariableComparisonSimplification.h"

namespace smtrat::qe::coverings::util {

FormulaT simplify(const FormulaT& input) {
    util::VariableComparisonSimplification simplifier(input);
    auto [simplified, change] = simplifier.getResult();
    while(change){
        util::VariableComparisonSimplification inner(simplified);
        std::tie(simplified, change) = inner.getResult();
    }
    return simplified;
}

std::size_t count_atoms(const FormulaT& f) {
    size_t result = 0 ;
    carl::visit(f, [&](const FormulaT& f){
        if(f.is_atom()){
            result++;
        }
    });
    return result;
}

}