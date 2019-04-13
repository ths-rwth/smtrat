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
        std::function<carl::Variable(Minisat::Var)> carlVar;
        std::function<Minisat::Var(carl::Variable)> minisatVar;
        // std::function<const auto&()> booleanConstraintMap;
        std::function<bool(Minisat::Var)> isTheoryAbstraction;
        std::function<const FormulaT&(Minisat::Var)> reabstractVariable;

    public:
        template<typename BaseModule>
        VarSchedulerMcsatBase(BaseModule& baseModule) :
            VarSchedulerBase(baseModule),
            isTheoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.isTheoryVar(v); }),
            carlVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.carlVar(v); }),
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
    template<mcsat::VariableOrdering vot>
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
            std::vector<carl::Variable> tordering = mcsat::calculate_variable_order<vot>(c);
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
                return 0;
            const auto& reabstraction = reabstractVariable(v);

            carl::Variables vars;
            reabstraction.arithmeticVars(vars);
            if (vars.empty())
                return 0;
            for (std::size_t i = ordering.size(); i > 0; i--) {
                if (vars.find(carlVar(ordering[i-1])) != vars.end()) {
                    return i;
                }
            }
            return 0;
        }

    };

    /**
     * Variable scheduling that all decides Boolean variables first before
     * deciding any theory variable.
     */
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatBooleanFirst : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        TheoryVarSchedulerStatic<vot> theory_ordering;
        
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
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking Boolean var");
                return boolean_ordering.pop();
            } else if (!theory_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking theory var");
                return theory_ordering.pop();
            } else {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "No variable available");
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
     * Variable scheduling that all decides theory variables first before
     * deciding any Boolean variable.
     */
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatTheoryFirst : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        TheoryVarSchedulerStatic<vot> theory_ordering;
        
    public:
        template<typename BaseModule>
        explicit VarSchedulerMcsatTheoryFirst( BaseModule& baseModule ) :
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
            if (!theory_ordering.empty()) {
                return theory_ordering.top();
            } else if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else {
                return var_Undef;
            }
        }

        Minisat::Var pop() {
            if (!theory_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking theory var");
                return theory_ordering.pop();
            } else if (!boolean_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking Boolean var");
                return boolean_ordering.pop();
            } else {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "No variable available");
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
    template<int lookahead, mcsat::VariableOrdering vot>
    class VarSchedulerMcsatUnivariateConstraintsOnly : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        TheoryVarSchedulerStatic<vot> theory_ordering;

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
                if (varDecidable(boolean_ordering.top())) {
                    SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking Boolean var");
                    return boolean_ordering.pop();
                } else {
                    SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Decision of next Boolean variable is deferred");
                    assert(!theory_ordering.empty());
                }
            }
            if (!theory_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking theory var");
                return theory_ordering.pop();
            }
            SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "No variable availabe");
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
            boolean_ordering.rebuild();
        }
    };


    /**
     * Activity-based scheduler preferring initially theory variables.
     */
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatActivityPreferTheory : public VarSchedulerMcsatBase {
        bool initialized = false;
        std::vector<Minisat::Var> theory_ordering;
        VarSchedulerMinisat ordering;

        auto compareVars(Minisat::Var x, Minisat::Var y) {
            if (getActivity(x) != getActivity(y)) {
                return getActivity(x) > getActivity(y);
            } else if (isTheoryVar(x) && !isTheoryVar(y)) {
                return true;
            } else if (!isTheoryVar(x) && isTheoryVar(y)) {
                return false;
            } else if (isTheoryVar(x) && isTheoryVar(y)) {
                auto ypos = std::find(theory_ordering.begin(), theory_ordering.end(), y);
                assert(!initialized || ypos != theory_ordering.end());
                return std::find(theory_ordering.begin(), ypos, x) != theory_ordering.end();
            } else { // !isTheoryVar(x) && !isTheoryVar(y)
                return false;
            }
        }

    public:

        template<typename BaseModule>
        explicit VarSchedulerMcsatActivityPreferTheory( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule),
            ordering( baseModule, [this](Minisat::Var x, Minisat::Var y) -> bool { return compareVars(x, y); } )
        {} 

        void rebuild() {
            ordering.rebuild();
        }

        void insert(Minisat::Var var) {
            ordering.insert(var);
        }

        Minisat::Var top() {
            return ordering.top();
        }

        Minisat::Var pop() {
            return ordering.pop();
        }

        bool empty() {
            return ordering.empty();
        }

        bool contains(Minisat::Var var) {
            return ordering.contains(var);
        }

        void print() const {
            ordering.print();
        }

        // Events called by SATModule

        void increaseActivity(Minisat::Var var) {
            ordering.increaseActivity(var);
        }

        void decreaseActivity(Minisat::Var var) {
            ordering.decreaseActivity(var);
        }

        void rebuildActivities() { 
            ordering.rebuild();
        }

        template<typename Constraints>
        void rebuildTheoryVars(const Constraints& c) {
            assert(!initialized);
            std::vector<carl::Variable> tordering = mcsat::calculate_variable_order<vot>(c);
            theory_ordering.clear();
            for (const auto& tvar : tordering) {
                theory_ordering.push_back(minisatVar(tvar));
            }
            initialized = true;
        }
    };

}