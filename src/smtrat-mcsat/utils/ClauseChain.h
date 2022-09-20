#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat {
namespace mcsat {


/**
 * An explanation is either a single clause or a chain of clauses, satisfying the following properties:
 * - If the clauses are inserted and propagated in the chain's order, at least the last clause should be conflicting.
 * - Each conflicting clause is already conflicting after preceding clauses have been inserted and propagated.
 * - Tseitin vars should be used so that a Tseitin variable C is equivalent to its corresponding subformula F (or at least C -> F).
 */
class ClauseChain {
    public:
        struct Link {
            private:
                FormulaT mClause;
                std::optional<FormulaT> mImpliedTseitinLiteral;

            public:
                Link(const FormulaT&& clause, const FormulaT&& impliedTseitinLiteral) :
                    mClause(clause), mImpliedTseitinLiteral(impliedTseitinLiteral) {}

                Link(const FormulaT&& clause) :
                    mClause(clause), mImpliedTseitinLiteral(std::nullopt) {};

                bool isPropagating() const {
                    return mImpliedTseitinLiteral && (*mImpliedTseitinLiteral).type() != carl::FormulaType::FALSE;
                }

                bool isConflicting() const {
                    return mImpliedTseitinLiteral && (*mImpliedTseitinLiteral).type() == carl::FormulaType::FALSE;
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
         * The returned variable C should be used so that C <-> formula or at least ~formula -> ~C
         */
        FormulaT createTseitinVar(const FormulaT& formula) {
            FormulaT var = carl::FormulaPool<smtrat::Poly>::getInstance().createTseitinVar(formula);
            mTseitinVars.insert(var);
            return var;
        }

        /**
         * Append a clause that implies impliedTseitinLiteral under the current assignment.
         * Note that impliedTseitinLiteral = ~v for a Tseitin variable v obtained via createTseitinVar.
         */
        void appendPropagating(const FormulaT&& clause, const FormulaT&& impliedTseitinLiteral) {
            mClauseChain.emplace_back(std::move(clause), std::move(impliedTseitinLiteral));
        }

        /**
         * Append a conflicting clause (regarding the current assignment).
         */
        void appendConflicting(const FormulaT&& clause) {
            mClauseChain.emplace_back(std::move(clause), FormulaT(carl::FormulaType::FALSE));
        }

        /**
         * Append an additional clause which is neither propagating nor conflicting. Can be used to
         * pass additional knowledge.
         */
        void appendOptional(const FormulaT&& clause) {
            mClauseChain.emplace_back(std::move(clause));
        }

        /**
         * @return A vector representing this chain.
         */
        const std::vector<Link>& chain() const {
            return mClauseChain;
        }

        /**
         * @return A constant iterator to the beginning of this chain.
         */
        const_iterator begin() const {
            return mClauseChain.begin();
        }

        /**
         * @return A constant iterator to the end of this chain.
         */
        const_iterator end() const {
            return mClauseChain.end();
        }

        /**
         * Performs resolution on the chain. Uses the last clause for resolution.
         * @return A single clause conflicting under the current assignment.
         */
        FormulaT resolve() const;

        /**
         * Transforms the clause chain into a formula (containing Tseitin variables).
         */
        FormulaT to_formula() const;

        /**
         * Transforms a given Boolean conjunction over AND and OR to CNF via Tseitin-Transformation
         * so that, if the input formula is conflicting under the current assignment, after all clauses
         * in "implications" have been propagated in the given order, the returned formula evaluates to false.
         */
        static ClauseChain from_formula(const FormulaT& f, const Model& model, bool with_equivalence);
};

inline std::ostream& operator<< (std::ostream& stream, const ClauseChain::Link& link) {
    if (link.isOptional()) {
        stream << link.clause();
    } else if (link.isPropagating()) {
        stream << link.clause() << " -> " << link.impliedTseitinLiteral();
    } else if (link.isConflicting()) {
        stream << link.clause() << " -> CONFLICT";
    }
	return stream;
}

inline std::ostream& operator<< (std::ostream& stream, const ClauseChain& chain) {
    stream << "[";
    for (auto iter = chain.begin(); iter != chain.end(); iter++) {
        stream << (*iter);
        if (iter != chain.end()-1)
            stream << ", ";
    }
    stream << "]" << std::endl;
	return stream;
}

}
}