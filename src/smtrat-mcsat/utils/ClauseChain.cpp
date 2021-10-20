#include "ClauseChain.h"

namespace smtrat::mcsat {

FormulaT ClauseChain::resolve() const {
    FormulasT result;
    std::unordered_set<FormulaT> toProcess;

    // initialize with conflicting clause
    assert(mClauseChain.back().isConflicting());
    if (mClauseChain.back().clause().isNary()) {
        for (const auto& lit : mClauseChain.back().clause()) {
            if (isTseitinVar(lit)) {
                toProcess.insert(lit);
            } else {
                result.push_back(lit);
            }
        }
    } else {
        if (isTseitinVar(mClauseChain.back().clause())) {
            toProcess.insert(mClauseChain.back().clause());
        } else {
            result.push_back(mClauseChain.back().clause());
        }
    }
    

    // resolve using propagations
    for (auto iter = mClauseChain.rbegin()+1; iter != mClauseChain.rend(); iter++) {
        if (iter->isPropagating()) {
            // check if any tseitin variable can be resolved using this clause
            if (toProcess.find(iter->impliedTseitinLiteral().negated()) == toProcess.end()) {
                continue;
            }

            // remove the processed tseitin variable
            toProcess.erase(iter->impliedTseitinLiteral().negated());

            // add literals of clauses to respective sets
            if (iter->clause().isNary()) {
                for (const auto& lit : iter->clause().subformulas()) {
                    if (lit != iter->impliedTseitinLiteral()) {
                        if (isTseitinVar(lit)) {
                            toProcess.insert(lit);
                        } else {
                            result.push_back(lit);
                        }
                    }
                }
            }
            
            if (toProcess.empty()) {
                break;
            }
        }
    }
    assert(toProcess.empty());

    return FormulaT(carl::FormulaType::OR, std::move(result));
}

FormulaT ClauseChain::to_formula() const {
    FormulasT fs;
    for (const auto& link : mClauseChain) {
        fs.push_back(link.clause());
    }
    return FormulaT(carl::FormulaType::AND, std::move(fs));
}

FormulaT _transformToImplicationChain(const FormulaT& formula, const Model& model, ClauseChain& chain, bool withEquivalences) {
    switch(formula.getType()) {
        case carl::FormulaType::TRUE:
        case carl::FormulaType::FALSE:
        case carl::FormulaType::CONSTRAINT:
        case carl::FormulaType::VARCOMPARE:
        case carl::FormulaType::VARASSIGN:
        {
            return formula;
        }
        break;

        case carl::FormulaType::OR:
        {
            FormulasT newFormula;
            for (const auto& sub : formula.subformulas()) {
                FormulaT tseitinSub = _transformToImplicationChain(sub, model, chain, withEquivalences);
                newFormula.push_back(std::move(tseitinSub));
            }
            return FormulaT(carl::FormulaType::OR, std::move(newFormula));
        }
        break;

        case carl::FormulaType::AND:
        {
            FormulaT tseitinVar = chain.createTseitinVar(formula);
            FormulasT newFormula;
            for (const auto& sub : formula.subformulas()) {
                FormulaT tseitinSub = _transformToImplicationChain(sub, model, chain, withEquivalences);
                newFormula.push_back(std::move(tseitinSub));
                const auto& lit = newFormula.back();

                // tseitinVar -> newFormula_1 && ... && newFormula_n

                carl::ModelValue<Rational,Poly> eval = carl::model::evaluate(sub, model);
                assert(eval.isBool());
                if (!eval.asBool()) {
                    chain.appendPropagating(FormulaT(carl::FormulaType::OR, FormulasT({lit, tseitinVar.negated()})), tseitinVar.negated());
                } else {
                    chain.appendOptional(FormulaT(carl::FormulaType::OR, FormulasT({lit, tseitinVar.negated()})));
                }
            }

            if (withEquivalences) {
                // newFormula_1 && ... && newFormula_n -> tseitinVar
                FormulasT tmp;
                std::transform (newFormula.begin(), newFormula.end(), std::back_inserter(tmp), [](const FormulaT& f) -> FormulaT { return f.negated(); } );
                tmp.push_back(tseitinVar);
                chain.appendOptional(FormulaT(carl::FormulaType::OR, tmp));
            }
            
            return tseitinVar;
        }

        default:
            SMTRAT_LOG_WARN("smtrat.mcsat", "Invalid formula type " << formula);
            assert(false);
            return FormulaT();
    }
}

ClauseChain ClauseChain::from_formula(const FormulaT& formula, const Model& model, bool with_equivalence) {
    ClauseChain chain;
    FormulaT conflictingClause = _transformToImplicationChain(formula, model, chain, with_equivalence);
    chain.appendConflicting(std::move(conflictingClause));
    return chain;
}


}