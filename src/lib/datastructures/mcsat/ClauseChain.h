#pragma once

#include "../../Common.h"

namespace smtrat {
namespace mcsat {


/**
* An explanation is either a single clause or a chain of clauses, satisfying the following properties:
* - If the clauses are inserted and propagated in the chain's order, at least the last clause should be conflicting.
* - Each conflicting clause is already conflicting after preceding clauses have been inserted and propagated.
* - Tseitin vars should be used...
* TODO describe
*/


class ClauseChain {
    public:
        struct Link {
            private:
                FormulaT mClause;
                boost::optional<FormulaT> mImpliedTseitinLiteral;

            public:
                Link(const FormulaT&& clause, const FormulaT&& impliedTseitinLiteral) :
                    mClause(clause), mImpliedTseitinLiteral(impliedTseitinLiteral) {}

                Link(const FormulaT&& clause) :
                    mClause(clause), mImpliedTseitinLiteral(boost::none) {};

                bool isPropagating() const {
                    return mImpliedTseitinLiteral && (*mImpliedTseitinLiteral).getType() != carl::FormulaType::FALSE;
                }

                bool isConflicting() const {
                    return mImpliedTseitinLiteral && (*mImpliedTseitinLiteral).getType() == carl::FormulaType::FALSE;
                }

                bool isOptional() const {
                    return !mImpliedTseitinLiteral;
                }

                const FormulaT& clause() const {
                    return mClause;
                }

                const FormulaT& impliedTseitinLiteral() const {
                    assert(isPropagating());
                    return *mImpliedTseitinLiteral;
                }

                friend std::ostream& operator<< (std::ostream& stream, const Link& link);
        };

        using const_iterator = typename std::vector<Link>::const_iterator;

        friend std::ostream& operator<< (std::ostream& stream, const ClauseChain& chain);
    
    private:
        std::vector<Link> mClauseChain;
        std::unordered_set<FormulaT> mTseitinVars;

        bool isTseitinVar(const FormulaT& var) const {
            return mTseitinVars.find(var) != mTseitinVars.end();
        }

    public:
        ClauseChain() {}

        /**
         * Create a Tseitin variable for the given formula.
         * The returned variable C should be used so that C <-> formula or at least ~C -> ~formula
         */
        FormulaT createTseitinVar(const FormulaT& formula) {
            FormulaT var = carl::FormulaPool<smtrat::Poly>::getInstance().createTseitinVar(formula);
            mTseitinVars.insert(var);
            return var;
        }

        void appendPropagating(const FormulaT&& clause, const FormulaT&& impliedTseitinLiteral) {
            mClauseChain.emplace_back(std::move(clause), std::move(impliedTseitinLiteral));
        }

        void appendConflicting(const FormulaT&& clause) {
            mClauseChain.emplace_back(std::move(clause), FormulaT(carl::FormulaType::FALSE));
        }

        void appendOptional(const FormulaT&& clause) {
            mClauseChain.emplace_back(std::move(clause));
        }

        const std::vector<Link>& chain() const {
            return mClauseChain;
        }

        /**
         * @return A constant iterator to the beginning of the list of sub-formulas of this formula.
         */
        const_iterator begin() const {
            return mClauseChain.begin();
        }

        /**
         * @return A constant iterator to the end of the list of sub-formulas of this formula.
         */
        const_iterator end() const {
            return mClauseChain.end();
        }

        FormulaT resolve() const {
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
};

inline std::ostream& operator<< (std::ostream& stream, const ClauseChain::Link& link) {
    if (link.isOptional()) {
        stream << link.clause();
    } else if (link.isPropagating()) {
        stream << link.clause() << " -> " << link.impliedTseitinLiteral();
    } else if (link.isConflicting()) {
        stream << link.clause() << " -> FALSE";
    }
}

inline std::ostream& operator<< (std::ostream& stream, const ClauseChain& chain) {
    stream << "[";
    for (auto iter = chain.begin(); iter != chain.end(); iter++) {
        stream << (*iter);
        if (iter != chain.end()-1)
            stream << ", ";
    }
    stream << "]" << std::endl;
}

}
}