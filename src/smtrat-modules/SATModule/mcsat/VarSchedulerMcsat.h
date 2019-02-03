#include "../VarScheduler.h"
#include <smtrat-mcsat/smtrat-mcsat.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>


namespace smtrat {
    /**
     * Base class for all MCSAT variable scheduler.
     */
    class VarSchedulerMcsatBase : public VarSchedulerBase {

    protected:
        std::function<bool(Minisat::Var)> isTheoryVar;
        std::function<carl::Variable(Minisat::Var)> theoryVar;
        std::function<Minisat::Var(carl::Variable)> minisatVar;

    public:
        template<typename BaseModule>
        VarSchedulerMcsatBase(BaseModule& baseModule) :
            VarSchedulerBase(baseModule),
            isTheoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.isTheoryVar(v); }),
            theoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.theoryVar(v); }),
            minisatVar([&baseModule](carl::Variable v){ return baseModule.mMCSAT.minisatVar(v); })
        {}
    };

    /**
     * Variable scheduling that all decides Boolean variables first before
     * deciding any theory variable.
     */
    class VarSchedulerMcsatBooleanFirst : public VarSchedulerMcsatBase {
        
        VarSchedulerMinisat boolean_ordering;
        std::vector<Minisat::Var> theory_ordering;
        std::vector<Minisat::Var>::const_iterator nextTheoryVar = theory_ordering.end();

    protected:
        bool valid(Minisat::Var var) {
            return isDecisionVar(var) && isBoolValueUndef(var);
        }

    public:
        template<typename BaseModule>
        explicit VarSchedulerMcsatBooleanFirst( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule),
            boolean_ordering( baseModule )
        {}

        void rebuild() {
            boolean_ordering.rebuild();
        }

        void insert(Minisat::Var var) {
            if (isTheoryVar(var)) {
                theory_ordering.push_back(var);
            } else {
                boolean_ordering.insert(var);
            }
        }

        Minisat::Var top() {
            if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else if (nextTheoryVar != theory_ordering.end()) {
                return *nextTheoryVar;
            } else {
                return var_Undef;
            }
        }

        Minisat::Var pop() {
            if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else if (nextTheoryVar != theory_ordering.end()) {
                auto next = *nextTheoryVar;
                nextTheoryVar++;
                return next;
            } else {
                return var_Undef;
            }
        }

        bool empty() {
            return boolean_ordering.empty() && nextTheoryVar == theory_ordering.end();
        }

        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return std::find(theory_ordering.begin(), theory_ordering.end(), var) != theory_ordering.end();
            } else {
                return boolean_ordering.contains(var);
            }
        }

        void print() const {
            boolean_ordering.print();
            std::cout << "Theory variable ordering: " << theory_ordering << std::endl;
        }

        // Events called by SATModule

        void increaseActivity(Minisat::Var var) {
            boolean_ordering.increaseActivity(var);
        }

        void decreaseActivity(Minisat::Var var) {
            boolean_ordering.decreaseActivity(var);
        }

        void rebuildActivities() { 
            boolean_ordering.rebuild();
        }

        template<typename Constraints>
        void rebuildTheoryVars(const Constraints& c) {
            // TODO DYNSCHED settings ...
            std::vector<carl::Variable> tordering = mcsat::calculate_variable_order<mcsat::VariableOrdering::FeatureBased>(c);
            assert(tordering.size() == theory_ordering.size());
            theory_ordering.clear();
            for (const auto& tvar : tordering) {
                theory_ordering.push_back(minisatVar(tvar));
            }
        }
    };
}