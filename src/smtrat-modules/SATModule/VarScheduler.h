#pragma once

#include "SolverTypes.h"
#include "Heap.h"
#include <functional>
#include <random>

namespace smtrat
{
    /**
     * Base class for variable schedulers. Removes the need to implement stubs.
     * 
     * During instantiation, the Scheduler is constructed with a const SATModule& as parameter.
     */
    class VarSchedulerBase {

    protected:
        std::function<double(Minisat::Var)> getActivity;
        std::function<char(Minisat::Var)> getPolarity;
        std::function<void(Minisat::Var,bool)> setPolarity;
        std::function<bool(Minisat::Var)> isDecisionVar;
        std::function<bool(Minisat::Var)> isBoolValueUndef;
        std::function<bool(Minisat::Var)> isTheoryAbstraction;
        std::function<const FormulaT&(Minisat::Var)> reabstractVariable;
        std::function<const FormulaT&(Minisat::Lit)> reabstractLiteral;
        std::function<const Minisat::Clause&(Minisat::CRef)> getClause;
        std::function<Minisat::lbool(Minisat::Var)> getBoolVarValue;
        std::function<Minisat::lbool(Minisat::Lit)> getBoolLitValue;
        std::function<unsigned(const FormulaT&)> currentlySatisfiedByBackend;
        std::function<const Minisat::Var(const FormulaT&)> abstractVariable;
        std::function<const Minisat::Lit(const FormulaT&)> abstractLiteral;
        std::function<bool(const FormulaT&)> isAbstractedFormula;

    public:
        template<typename BaseModule>
        VarSchedulerBase(BaseModule& baseModule) :
            getActivity([&baseModule](Minisat::Var v){ return baseModule.activity[v]; }),
            getPolarity([&baseModule](Minisat::Var v){ return baseModule.polarity[v]; }),
            setPolarity([&baseModule](Minisat::Var v, bool p){ return baseModule.polarity[v] = p; }),
            isDecisionVar([&baseModule](Minisat::Var v){ return baseModule.decision[v]; }),
            isBoolValueUndef([&baseModule](Minisat::Var v){ return baseModule.bool_value(v) == l_Undef; }),
            isTheoryAbstraction([&baseModule](Minisat::Var v){ return (baseModule.mBooleanConstraintMap.size() > v) && (baseModule.mBooleanConstraintMap[v].first != nullptr); }),
            reabstractVariable([&baseModule](Minisat::Var v) -> const auto& { return baseModule.mBooleanConstraintMap[v].first->reabstraction; }),
            reabstractLiteral([&baseModule](Minisat::Lit l) -> const auto& { return Minisat::sign(l) ? baseModule.mBooleanConstraintMap[Minisat::var(l)].second->reabstraction : baseModule.mBooleanConstraintMap[Minisat::var(l)].first->reabstraction; }),
            getClause([&baseModule](Minisat::CRef cl) -> const auto& { return baseModule.getClause(cl); }),
            getBoolVarValue([&baseModule](Minisat::Var v){ return baseModule.bool_value(v); }),
            getBoolLitValue([&baseModule](Minisat::Lit l){ return baseModule.bool_value(l); }),
            currentlySatisfiedByBackend([&baseModule](const FormulaT& f){ return baseModule.currentlySatisfiedByBackend(f); }),
            abstractVariable([&baseModule](const FormulaT& f) { return Minisat::var(baseModule.mConstraintLiteralMap.at(f).front()); }),
            abstractLiteral([&baseModule](const FormulaT& f) { return baseModule.mConstraintLiteralMap.at(f).front(); }),
            isAbstractedFormula([&baseModule](const FormulaT& f) { return baseModule.mConstraintLiteralMap.count(f) > 0; })
        {}

        /**
         * Rebuild heap.
         */
        void rebuild() { assert(false); }

        /**
         * Insert a variable. If already contained, do nothing. 
         */
        void insert(Minisat::Var)  { assert(false); }

        /**
         * Returns the next variable to be decided.
         */
        // Minisat::Var top() { assert(false); }

        /**
         * Returns and removes the next variable to be decided.
         */
        Minisat::Lit pop() { assert(false); }

        /**
         * Check if empty.
         */
        bool empty() {assert(false); }

        /**
         * Check if variable is contained.
         */
        // bool contains(Minisat::Var) { assert(false); }

        /**
         * Print.
         */
        void print() const { assert(false); }

        // Events called by SATModule

        void increaseActivity(Minisat::Var) {
        }

        void decreaseActivity(Minisat::Var) {
        }

        void rebuildActivities() {
        }

        template<typename Constraints>
        void rebuildTheoryVars(const Constraints&) {
        }

        void attachClause(Minisat::CRef /* cl */) {
        }

        void detachClause(Minisat::CRef /* cl */) {
        }

        void relocateClauses(std::function<void(Minisat::CRef&)> /* relocate */) {            
        }
    };

    /**
     * Minisat's activity-based variable scheduling.
     */
    class VarSchedulerMinisat : public VarSchedulerBase {
        struct VarOrderLt
        {
            std::function<bool(Minisat::Var,Minisat::Var)> cmp;

            bool operator ()( Minisat::Var x, Minisat::Var y )
            {
                return cmp(x,y);
            }

            explicit VarOrderLt( std::function<bool(Minisat::Var,Minisat::Var)> cmp ) :
                cmp( cmp )
            {}
        };

        Minisat::Heap<VarOrderLt> order_heap;

    protected:
        bool valid(Minisat::Var var) {
            return isDecisionVar(var) && isBoolValueUndef(var);
        }

    public:
        template<typename BaseModule>
        explicit VarSchedulerMinisat( BaseModule& baseModule, std::function<bool(Minisat::Var,Minisat::Var)> cmp ) :
            VarSchedulerBase( baseModule ),
            order_heap( VarOrderLt( cmp ) )
        {}

        template<typename BaseModule>
        explicit VarSchedulerMinisat( BaseModule& baseModule ) :
            VarSchedulerMinisat( baseModule, [this](Minisat::Var x, Minisat::Var y) -> bool { return getActivity(x) > getActivity(y); } )
        {}

        void rebuild() {
            Minisat::vec<Minisat::Var> vs;
            for(Minisat::Var v = 0; v < order_heap.size(); v++)
                if(order_heap.inHeap(v) && valid(v))
                    vs.push(v);
            order_heap.build(vs);
        }

        void insert(Minisat::Var var) {
            if (!order_heap.inHeap(var) && valid(var))
                order_heap.insert(var);
        }

        Minisat::Var top() {
            if (empty())
                return var_Undef;
            return order_heap[0];
        }

        Minisat::Lit pop() {
            if (empty())
                return Minisat::lit_Undef;
            auto next = order_heap.removeMin();
            return Minisat::mkLit( next, getPolarity(next) );
        }

        bool empty() {
            while(!order_heap.empty() && !valid(order_heap[0]))
                order_heap.removeMin();
            return order_heap.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            return order_heap.inHeap(var) && valid(var);
        }
        */

        void print() const {
            order_heap.print();
        }

        // Events called by SATModule

        void increaseActivity(Minisat::Var var) {
            if(order_heap.inHeap(var))
                order_heap.decrease(var);
        }

        void decreaseActivity(Minisat::Var var) {
            if(order_heap.inHeap(var))
                order_heap.increase(var);
        }

        void rebuildActivities() { 
            rebuild();
        }

    };

    class VarSchedulerFixedRandom : public VarSchedulerMinisat {
        std::vector<Minisat::Var> ordering;

    private:
        auto getIndex(Minisat::Var var) {
            auto iter = std::find(ordering.begin(), ordering.end(), var);
            if (iter == ordering.end()) {
                auto it = ordering.begin();
                long unsigned int idx = 0;
                if (ordering.size() > 0) {
                    std::random_device rd;
                    std::mt19937 gen(rd());
                    std::uniform_int_distribution<long unsigned int> dis(0, ordering.size()-1);
                    idx = dis(gen);
                }
                it += idx;
                iter = ordering.insert(it, var);
            }
            return iter;
        }

    public:
        template<typename BaseModule>
        explicit VarSchedulerFixedRandom( BaseModule& baseModule ) :
            VarSchedulerMinisat( baseModule, [this](Minisat::Var x, Minisat::Var y) { return getIndex(x) > getIndex(y); } )
        {}
    };

    /**
     * Random scheduler
     */
    class VarSchedulerRandom : public VarSchedulerBase {

        std::vector<Minisat::Var> vars;

        protected:
        bool valid(Minisat::Var var) {
            return isDecisionVar(var) && isBoolValueUndef(var);
        }

    public:
        template<typename BaseModule>
        explicit VarSchedulerRandom( BaseModule& baseModule ) :
            VarSchedulerBase( baseModule )
        {}

        void rebuild() {}

        void insert(Minisat::Var var) {
            if (std::find(vars.begin(), vars.end(), var) == vars.end() && valid(var)) {
                auto it = vars.begin();
                std::random_device rd;
                std::mt19937 gen(rd());
                std::uniform_int_distribution<long unsigned int> dis(0, vars.size()-1);
                it += dis(gen);
                vars.insert(it, var);
            }
        }

        /*
        Minisat::Var top() {
            if (empty())
                return var_Undef;
            return vars.back();
        }
        */

        Minisat::Lit pop() {
            if (empty())
                return Minisat::lit_Undef;
            auto res = vars.back();
            vars.pop_back();
            return Minisat::mkLit( res, getPolarity(res) );
        }

        bool empty() {
            while(!vars.empty() && !valid(vars.back()))
                vars.pop_back();
            return vars.empty();
        }

        /*
        bool contains(Minisat::Var var) {
            return std::find(vars.begin(), vars.end(), var) != vars.end() && valid(var);
        }
        */

        void print() const {
            std::cout << "Random scheduler contents: " << vars << std::endl;
        }
    };


    /**
     * Scheduler for SMT, implementing theory guided heuristics.
     */
    template<TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic>
    class VarSchedulerSMTTheoryGuided : public VarSchedulerBase {
        VarSchedulerMinisat minisat;

    public:
        template<typename BaseModule>
        explicit VarSchedulerSMTTheoryGuided( BaseModule& baseModule ) :
            VarSchedulerBase( baseModule ),
            minisat( baseModule )
        {}

        void rebuild() {
            minisat.rebuild();
        }

        void insert(Minisat::Var var) {
            minisat.insert(var);
        }

        Minisat::Lit pop() {
            Minisat::Var next = var_Undef;
            std::vector<Minisat::Var> varsToRestore;

            while (next == var_Undef) {
                if (minisat.empty()) {
                    next = var_Undef;
                    break;
                }
                else {
                    next = var(minisat.pop());

                    if (isTheoryAbstraction(next)) {
                        unsigned consistency = currentlySatisfiedByBackend(reabstractVariable(next));
                        bool skipVariable = false;
                        switch (theory_conflict_guided_decision_heuristic) {
                            case TheoryGuidedDecisionHeuristicLevel::CONFLICT_FIRST: {
                                switch (consistency) {
                                    case 0:
                                        setPolarity(next, false);
                                        break;
                                    case 1:
                                        setPolarity(next, true);
                                        break;
                                    default:
                                        skipVariable = true;
                                        break;
                                }
                                break;
                            }
                            case TheoryGuidedDecisionHeuristicLevel::SATISFIED_FIRST: {
                                switch (consistency) {
                                    case 0:
                                        setPolarity(next, true);
                                        break;
                                    case 1:
                                        setPolarity(next, false);
                                        break;
                                    default:
                                        skipVariable = true;
                                        break;
                                }
                                break;
                            }
                            default:
                                assert( theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::DISABLED );
                                break;
                        }
                        if (skipVariable) {
                            varsToRestore.push_back(next);
                            next = var_Undef;
                        }
                    }
                }
            }
            for (auto v : varsToRestore) {
                minisat.insert(v);
            }
            if (next == var_Undef) {
                return minisat.pop();
            } else {
                return Minisat::mkLit(next, getPolarity(next));
            }
        }

        bool empty() {
            return minisat.empty();
        }

        void print() const {
            minisat.print();
        }

        // Events called by SATModule

        void increaseActivity(Minisat::Var var) {
            minisat.increaseActivity(var);
        }

        void decreaseActivity(Minisat::Var var) {
            minisat.decreaseActivity(var);
        }

        void rebuildActivities() { 
            minisat.rebuildActivities();
        }

    };
}
