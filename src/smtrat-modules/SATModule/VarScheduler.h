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
        std::function<bool(Minisat::Var)> isDecisionVar;
        std::function<bool(Minisat::Var)> isBoolValueUndef;

    public:
        template<typename BaseModule>
        VarSchedulerBase(BaseModule& baseModule) :
            getActivity([&baseModule](Minisat::Var v){ return baseModule.activity[v]; }),
            isDecisionVar([&baseModule](Minisat::Var v){ return baseModule.decision[v]; }),
            isBoolValueUndef([&baseModule](Minisat::Var v){ return baseModule.bool_value(v) == l_Undef; }) {
        }

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
        Minisat::Var top() { assert(false); }

        /**
         * Returns and removes the next variable to be decided.
         */
        Minisat::Var pop() { assert(false); }

        /**
         * Check if empty.
         */
        bool empty() {assert(false); }

        /**
         * Check if variable is contained.
         */
        bool contains(Minisat::Var) { assert(false); }

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

        Minisat::Var pop() {
            if (empty())
                return var_Undef;
            return order_heap.removeMin();
        }

        bool empty() {
            while(!order_heap.empty() && !valid(order_heap[0]))
                order_heap.removeMin();
            return order_heap.empty();
        }

        bool contains(Minisat::Var var) {
            return order_heap.inHeap(var) && valid(var);
        }

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

    public:

        template<typename BaseModule>
        explicit VarSchedulerFixedRandom( BaseModule& baseModule ) :
            VarSchedulerMinisat( baseModule, [this](Minisat::Var x, Minisat::Var y) { return getIndex(x) > getIndex(y); } )
        {} 

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

        Minisat::Var top() {
            if (empty())
                return var_Undef;
            return vars.back();
        }

        Minisat::Var pop() {
            if (empty())
                return var_Undef;
            auto res = vars.back();
            vars.pop_back();
            return res;
        }

        bool empty() {
            while(!vars.empty() && !valid(vars.back()))
                vars.pop_back();
            return vars.empty();
        }

        bool contains(Minisat::Var var) {
            return std::find(vars.begin(), vars.end(), var) != vars.end() && valid(var);
        }

        void print() const {
            std::cout << "Random scheduler contents: " << vars << std::endl;
        }
    };
}
