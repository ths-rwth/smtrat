#include "../VarScheduler.h"
#include <smtrat-mcsat/smtrat-mcsat.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>


namespace smtrat {
    /**
     * Base class for all MCSAT variable scheduler.
     * 
     * Should not be used directly.
     */
    class VarSchedulerMcsatBase : public VarSchedulerBase {

    protected:
        std::function<bool(Minisat::Var)> isTheoryVar;
        std::function<carl::Variable(Minisat::Var)> theoryVar;
        std::function<Minisat::Var(carl::Variable)> minisatVar;
        // std::function<const auto&()> booleanConstraintMap;
        std::function<bool(Minisat::Var)> isTheoryAbstraction;
        std::function<const FormulaT&(Minisat::Var)> reabstractVariable;

    public:
        template<typename BaseModule>
        VarSchedulerMcsatBase(BaseModule& baseModule) :
            VarSchedulerBase(baseModule),
            isTheoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.isTheoryVar(v); }),
            theoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.theoryVar(v); }),
            minisatVar([&baseModule](carl::Variable v){ return baseModule.mMCSAT.minisatVar(v); }),
            isTheoryAbstraction([&baseModule](Minisat::Var v){ return (baseModule.mBooleanConstraintMap.size() > v) && (baseModule.mBooleanConstraintMap[v].first != nullptr); }),
            reabstractVariable([&baseModule](Minisat::Var v) -> const auto& { return baseModule.mBooleanConstraintMap[v].first->reabstraction; })
            // booleanConstraintMap([&baseModule]() -> const auto& { return baseModule.mBooleanConstraintMap; })
        {}
    };

    /**
     * Schedules theory variables statically.
     * 
     * Should not be used directly.
     */
    class TheoryVarSchedulerStatic : public VarSchedulerMcsatBase {
        std::vector<Minisat::Var> ordering;
        std::vector<Minisat::Var>::const_iterator nextTheoryVar = ordering.end();
        bool initialized = false;

    public:

        template<typename BaseModule>
        explicit TheoryVarSchedulerStatic( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule)
        {}

        void insert(Minisat::Var var) {
            if (!initialized) {
                ordering.push_back(var);
            } else {
                assert(*(nextTheoryVar - 1) == var);
                nextTheoryVar--;
            }  
        }

        bool empty() {
            return nextTheoryVar == ordering.end();
        }

        Minisat::Var top() {
            return *nextTheoryVar;
        }

        Minisat::Var pop() {
            auto next = *nextTheoryVar;
            nextTheoryVar++;
            return next;
        }

        bool contains(Minisat::Var var) {
            return std::find(ordering.begin(), ordering.end(), var) != ordering.end();
        }

        void print() const {
            std::cout << "Theory variable ordering: " << ordering << std::endl;
        }

        template<typename Constraints>
        void rebuildTheoryVars(const Constraints& c) {
            assert(!initialized);
            // const auto& c = booleanConstraintMap();
            // TODO DYNSCHED settings ...
            std::vector<carl::Variable> tordering = mcsat::calculate_variable_order<mcsat::VariableOrdering::FeatureBased>(c);
            assert(tordering.size() == ordering.size());
            ordering.clear();
            for (const auto& tvar : tordering) {
                ordering.push_back(minisatVar(tvar));
            }
            nextTheoryVar = ordering.begin();
            initialized = true;
        }

        // helper
        /**
         * Level of the next theory variable.
         */
        size_t level() {
            return nextTheoryVar - ordering.begin() + 1;
        }

        /**
         * Returns the level in which the given constraint is univariate
         */
        size_t univariateLevel(Minisat::Var v) {
            if (!isTheoryAbstraction(v)) 
                return 0; // TODO DYNSCHED how to handle non-theory abstractions?
            const auto& reabstraction = reabstractVariable(v);

            carl::Variables vars;
            reabstraction.arithmeticVars(vars);
            if (vars.empty())
                return 0;
            for (std::size_t i = ordering.size(); i > 0; i--) {
                if (vars.find(theoryVar(ordering[i-1])) != vars.end()) {
                    return i;
                }
            }
        }

    };

    /**
     * Variable scheduling that all decides Boolean variables first before
     * deciding any theory variable.
     */
    class VarSchedulerMcsatBooleanFirst : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        TheoryVarSchedulerStatic theory_ordering;
        
    public:
        template<typename BaseModule>
        explicit VarSchedulerMcsatBooleanFirst( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule),
            boolean_ordering( baseModule ),
            theory_ordering( baseModule )
        {}

        void rebuild() {
            boolean_ordering.rebuild();
        }

        void insert(Minisat::Var var) {
            if (isTheoryVar(var)) {
                theory_ordering.insert(var);              
            } else {
                boolean_ordering.insert(var);
            }
        }

        Minisat::Var top() {
            if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else if (!theory_ordering.empty()) {
                return theory_ordering.top();
            } else {
                return var_Undef;
            }
        }

        Minisat::Var pop() {
            if (!boolean_ordering.empty()) {
                return boolean_ordering.pop();
            } else if (!theory_ordering.empty()) {
                return theory_ordering.pop();
            } else {
                return var_Undef;
            }
        }

        bool empty() {
            return boolean_ordering.empty() && theory_ordering.empty();
        }

        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return theory_ordering.contains(var);
            } else {
                return boolean_ordering.contains(var);
            }
        }

        void print() const {
            boolean_ordering.print();
            theory_ordering.print();
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
            theory_ordering.rebuildTheoryVars(c);
        }
    };

    /**
     * Decides only Constraints univariate in the current theory variable while the
     * theory ordering is static.
     */
    template<int lookahead>
    class VarSchedulerMcsatUnivariateConstraintsOnly : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        TheoryVarSchedulerStatic theory_ordering;

        bool varCmp(Minisat::Var x, Minisat::Var y) {
            auto x_lvl = theory_ordering.univariateLevel(x);
            auto y_lvl = theory_ordering.univariateLevel(y);
            return x_lvl < y_lvl || (x_lvl == y_lvl && getActivity(x) > getActivity(y));
        }

        bool varDecidable(Minisat::Var x) {
            static_assert(lookahead >= 1);
            return theory_ordering.univariateLevel(x) <= theory_ordering.level() + lookahead;
        }
        
    public:
        template<typename BaseModule>
        explicit VarSchedulerMcsatUnivariateConstraintsOnly( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule),
            boolean_ordering( baseModule, [this](Minisat::Var x, Minisat::Var y) -> bool { return varCmp(x,y); } ),
            theory_ordering( baseModule )
        {}

        void rebuild() {
            boolean_ordering.rebuild();
        }

        void insert(Minisat::Var var) {
            if (isTheoryVar(var)) {
                theory_ordering.insert(var);              
            } else {
                boolean_ordering.insert(var);
            }
        }

        Minisat::Var top() {
            if (!boolean_ordering.empty()) {
                if (varDecidable(boolean_ordering.top()))
                    return boolean_ordering.top();
                else
                    assert(!theory_ordering.empty());
            }
            if (!theory_ordering.empty()) {
                return theory_ordering.top();
            }
            return var_Undef;
        }

        Minisat::Var pop() {
            if (!boolean_ordering.empty()) {
                if (varDecidable(boolean_ordering.top()))
                    return boolean_ordering.pop();
                else
                    assert(!theory_ordering.empty());
            }
            if (!theory_ordering.empty()) {
                return theory_ordering.pop();
            }
            return var_Undef;
        }

        bool empty() {
            return boolean_ordering.empty() && theory_ordering.empty();
        }

        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return theory_ordering.contains(var);
            } else {
                return boolean_ordering.contains(var);
            }
        }

        void print() const {
            boolean_ordering.print();
            theory_ordering.print();
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
            theory_ordering.rebuildTheoryVars(c);
        }
    };

}