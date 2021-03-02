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
        std::function<Model()> currentModel;
        // std::function<const auto&()> booleanConstraintMap;

    public:
        template<typename BaseModule>
        VarSchedulerMcsatBase(BaseModule& baseModule) :
            VarSchedulerBase(baseModule),
            isTheoryVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.isTheoryVar(v); }),
            carlVar([&baseModule](Minisat::Var v){ return baseModule.mMCSAT.carlVar(v); }),
            minisatVar([&baseModule](carl::Variable v){ return baseModule.mMCSAT.minisatVar(v); }),
            currentModel([&baseModule](){ return baseModule.mMCSAT.model(); })
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

        /*
        Minisat::Var top() {
            return *nextTheoryVar;
        }
        */

        Minisat::Lit pop() {
            if (empty()) {
                return Minisat::lit_Undef;
            }
            auto next = *nextTheoryVar;
            nextTheoryVar++;
            return Minisat::mkLit( next, true );
        }

        /*
        bool contains(Minisat::Var var) {
            return std::find(ordering.begin(), ordering.end(), var) != ordering.end();
        }
        */

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

            auto vars = carl::arithmetic_variables(reabstraction);
            if (vars.empty())
                return 0;
            for (std::size_t i = ordering.size(); i > 0; i--) {
                if (vars.has(carlVar(ordering[i-1]))) {
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

        /*
        Minisat::Var top() {
            if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else if (!theory_ordering.empty()) {
                return theory_ordering.top();
            } else {
                return var_Undef;
            }
        }
        */

        Minisat::Lit pop() {
            if (!boolean_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking Boolean var");
                return boolean_ordering.pop();
            } else if (!theory_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking theory var");
                return theory_ordering.pop();
            } else {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "No variable available");
                return Minisat::lit_Undef;
            }
        }

        bool empty() {
            return boolean_ordering.empty() && theory_ordering.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return theory_ordering.contains(var);
            } else {
                return boolean_ordering.contains(var);
            }
        }
        */

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
    // template<mcsat::VariableOrdering vot>
    template<typename TheoryScheduler>
    class VarSchedulerMcsatTheoryFirst : public VarSchedulerMcsatBase {
        VarSchedulerMinisat boolean_ordering;
        // TheoryVarSchedulerStatic<vot> theory_ordering;
        TheoryScheduler theory_ordering;
        
    public:
        template<typename BaseModule>
        explicit VarSchedulerMcsatTheoryFirst( BaseModule& baseModule ) :
            VarSchedulerMcsatBase(baseModule),
            boolean_ordering( baseModule ),
            theory_ordering( baseModule )
        {}

        void rebuild() {
            boolean_ordering.rebuild();
            theory_ordering.rebuild();
        }

        void insert(Minisat::Var var) {
            if (isTheoryVar(var)) {
                theory_ordering.insert(var);              
            } else {
                boolean_ordering.insert(var);
            }
        }

        /*
        Minisat::Var top() {
            if (!theory_ordering.empty()) {
                return theory_ordering.top();
            } else if (!boolean_ordering.empty()) {
                return boolean_ordering.top();
            } else {
                return var_Undef;
            }
        }
        */

        Minisat::Lit pop() {
            if (!theory_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking theory var");
                return theory_ordering.pop();
            } else if (!boolean_ordering.empty()) {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "Picking Boolean var");
                return boolean_ordering.pop();
            } else {
                SMTRAT_LOG_DEBUG("smtrat.sat.mcsat.scheduler", "No variable available");
                return Minisat::lit_Undef;
            }
        }

        bool empty() {
            return boolean_ordering.empty() && theory_ordering.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return theory_ordering.contains(var);
            } else {
                return boolean_ordering.contains(var);
            }
        }
        */

        void print() const {
            boolean_ordering.print();
            theory_ordering.print();
        }

        // Events called by SATModule

        void increaseActivity(Minisat::Var var) {
            boolean_ordering.increaseActivity(var);
            theory_ordering.increaseActivity(var);
        }

        void decreaseActivity(Minisat::Var var) {
            boolean_ordering.decreaseActivity(var);
            theory_ordering.decreaseActivity(var);
        }

        void rebuildActivities() { 
            boolean_ordering.rebuild();
            theory_ordering.rebuild();
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

        /*
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
        */

        Minisat::Lit pop() {
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
            return Minisat::lit_Undef;
        }

        bool empty() {
            return boolean_ordering.empty() && theory_ordering.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            if (isTheoryVar(var)) {
                return theory_ordering.contains(var);
            } else {
                return boolean_ordering.contains(var);
            }
        }
        */

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
     * Decides only Constraints occuring in clauses that are univariate in the current
     * theory variable while the theory ordering is static.
     * This corresponds to the original NLSAT strategy.
     */
    template<typename TheoryScheduler, bool respectActivities>
    class VarSchedulerMcsatUnivariateClausesOnly : public VarSchedulerMcsatBase {
        private:
            bool univariate(Minisat::CRef cl) {
                const auto& x = mTheoryLevels.back().variable;

                for (int i = 0; i < getClause(cl).size(); i++) {
                    const auto& l = getClause(cl)[i];
                    if (isTheoryAbstraction(Minisat::var(l))) {
                        const auto& reabstraction = reabstractLiteral(l);

                        const auto substituted = carl::model::substitute(reabstraction, currentModel());

                        auto vars = carl::arithmetic_variables(substituted);

                        auto size = arithmeticVars.size();
                        for (auto iter = mTheoryLevels.begin(); iter != std::prev(mTheoryLevels.end()); iter++) {
                            if (vars.has(iter->variable)){
                                size --;
                            }
                        }

                        if (size == 0)
                            continue;
                        if (size > 1 || !vars.has(x)) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                return true;
            }

            bool decidedByTheory(Minisat::CRef cl) {
                for (int i = 0; i < getClause(cl).size(); i++) {
                    const auto& l = getClause(cl)[i];
                    if (isTheoryAbstraction(Minisat::var(l))) {
                        const auto& eval = carl::model::evaluate(reabstractLiteral(l), currentModel());
                        if (!eval.isBool()) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                return true;
            }

            Minisat::Lit undefLitIn(Minisat::CRef cl) {
                Minisat::Lit res = Minisat::lit_Undef;
                for (int i = 0; i < getClause(cl).size(); i++) {
                    auto lit = getClause(cl)[i];
                    if (getBoolLitValue(lit) == l_Undef) {
                        if (!respectActivities) {
                            return lit;
                        }
                        if (res == Minisat::lit_Undef || getActivity(Minisat::var(res)) < getActivity(Minisat::var(lit))) {
                            res = lit;
                        }
                    }
                }
                return res;
            }

            struct TheoryLevel {
                std::vector<Minisat::CRef> clauses;
                carl::Variable variable;
            };

            std::vector<Minisat::CRef> mUndecidedClauses;
            std::vector<TheoryLevel> mTheoryLevels;

            TheoryScheduler theory_ordering;


            Minisat::Lit pickBooleanVarFromCurrentLevel() {
                assert(mTheoryLevels.back().variable != carl::Variable::NO_VARIABLE);
                Minisat::Lit res = Minisat::lit_Undef;
                for (const auto& cl : mTheoryLevels.back().clauses) {
                    auto lit = undefLitIn(cl);
                    if (lit != Minisat::lit_Undef) {
                        if (!respectActivities) {
                            return lit;
                        }
                        if (res == Minisat::lit_Undef || getActivity(Minisat::var(res)) < getActivity(Minisat::var(lit))) {
                            res = lit;
                        }
                    }
                }
                return res;
            }


            Minisat::Lit pickBooleanVarFromUndecided() {
                assert(mTheoryLevels.back().variable == carl::Variable::NO_VARIABLE);
                Minisat::Lit res = Minisat::lit_Undef;
                for (const auto& cl : mUndecidedClauses) {
                    auto lit = undefLitIn(cl);
                    if (lit != Minisat::lit_Undef) {
                        if (!respectActivities) {
                            return lit;
                        }
                        if (res == Minisat::lit_Undef || getActivity(Minisat::var(res)) < getActivity(Minisat::var(lit))) {
                            res = lit;
                        }
                    }
                }
                return res;
            }


            carl::Variable theoryDecision() {
                // precondition: all clauses in mTheoryLevels.back().clauses should be satisfied (by Boolean/theory)!
                assert(mTheoryLevels.back().variable != carl::Variable::NO_VARIABLE);
                carl::Variable& v = mTheoryLevels.back().variable;
                mTheoryLevels.emplace_back();
                return v;
            }
            

            bool pickNextTheoryVar() {
                assert(mTheoryLevels.back().variable == carl::Variable::NO_VARIABLE);
                for (auto cl = mUndecidedClauses.begin(); cl != mUndecidedClauses.end();) {
                    if (decidedByTheory(*cl)) {
                        mTheoryLevels[mTheoryLevels.size()-2].clauses.push_back(*cl);
                        cl = mUndecidedClauses.erase(cl);
                    } else {
                        cl++;
                    }
                }
                auto lit = theory_ordering.pop();
                if (lit == Minisat::lit_Undef) {
                    return false;
                }
                mTheoryLevels.back().variable = carlVar(Minisat::var(lit));
                for (auto cl = mUndecidedClauses.begin(); cl != mUndecidedClauses.end();) {
                    if (univariate(*cl)) {
                        mTheoryLevels.back().clauses.push_back(*cl);
                        cl = mUndecidedClauses.erase(cl);
                    } else {
                        cl++;
                    }
                }
                return true;
            }

            void popTheoryLevel() {
                assert(mTheoryLevels.size() > 1);

                if (mTheoryLevels.back().variable != carl::Variable::NO_VARIABLE) {
                    auto v = mTheoryLevels.back().variable;
                    theory_ordering.insert(minisatVar(v));
                }

                mUndecidedClauses.insert(mUndecidedClauses.end(), mTheoryLevels.back().clauses.begin(), mTheoryLevels.back().clauses.end());
                mTheoryLevels.pop_back();

                assert(mTheoryLevels.back().variable != carl::Variable::NO_VARIABLE);
            }

        public:

            void attachClause(Minisat::CRef cl) {
                // We only allow attaching clauses of level >= current level
                // which is the case for learned clauses.
                if (univariate(cl)) {
                    mTheoryLevels.back().clauses.push_back(cl);
                } else {
                    assert(!decidedByTheory(cl));
                    mUndecidedClauses.push_back(cl);
                }
            }

            void detachClause(Minisat::CRef cl) {
                mUndecidedClauses.erase(std::remove(mUndecidedClauses.begin(), mUndecidedClauses.end(), cl), mUndecidedClauses.end());
                for (auto& level : mTheoryLevels) {
                    level.clauses.erase(std::remove(level.clauses.begin(), level.clauses.end(), cl), level.clauses.end());
                }
            }

            void relocateClauses(std::function<void(Minisat::CRef&)> relocate) {
                for (auto& level : mTheoryLevels) {
                    for (auto& clause : level.clauses) {
                        relocate(clause);
                    }
                }  
                for (auto& clause : mUndecidedClauses) {
                    relocate(clause);
                }      
            }


        public:
            template<typename BaseModule>
            explicit VarSchedulerMcsatUnivariateClausesOnly( BaseModule& baseModule ) :
                VarSchedulerMcsatBase(baseModule),
                theory_ordering( baseModule )
            {
                mTheoryLevels.emplace_back();
            }

            void rebuild() {
                theory_ordering.rebuild();
            }

            void insert(Minisat::Var var) {
                if (isTheoryVar(var)) {
                    if (mTheoryLevels.back().variable != carl::Variable::NO_VARIABLE || mTheoryLevels.size() > 1) {
                        popTheoryLevel(); 
                        assert(mTheoryLevels.back().variable == carlVar(var));    
                    } else {
                        theory_ordering.insert(var);
                    }
                } else {
                    // do nothing
                }
            }

            Minisat::Lit pop() {
                if (mTheoryLevels.back().variable == carl::Variable::NO_VARIABLE) {
                    if (!pickNextTheoryVar()) {
                        // possibly undef, in this case, no decisions left
                        return pickBooleanVarFromUndecided();
                    }
                }
                auto res = pickBooleanVarFromCurrentLevel();
                if (res != Minisat::lit_Undef) {
                    return res;
                } else {
                    auto x = theoryDecision();
                    return Minisat::mkLit( minisatVar(x), true );
                }
            }

            bool empty() {
                return theory_ordering.empty() && pickBooleanVarFromCurrentLevel() == Minisat::lit_Undef;
            }

            void print() const {
                theory_ordering.print();
                for (const auto& level: mTheoryLevels) {
                    std::cout << "Clauses in " << level.variable << ": " << level.clauses << std::endl;
                }
                std::cout << "Undecided clauses: " << mUndecidedClauses << std::endl;
            }

            // Events called by SATModule

            void increaseActivity(Minisat::Var var) {
                theory_ordering.increaseActivity(var);
            }

            void decreaseActivity(Minisat::Var var) {
                theory_ordering.decreaseActivity(var);
            }

            void rebuildActivities() { 
                theory_ordering.rebuild();
            }

            template<typename Constraints>
            void rebuildTheoryVars(const Constraints& c) {
                assert(mTheoryLevels.size() == 1 && mTheoryLevels.back().variable == carl::Variable::NO_VARIABLE);
                theory_ordering.rebuildTheoryVars(c);
                pickNextTheoryVar();
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

        /*
        Minisat::Var top() {
            return ordering.top();
        }
        */

        Minisat::Lit pop() {
            return ordering.pop();
        }

        bool empty() {
            return ordering.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            return ordering.contains(var);
        }
        */

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