#pragma once

#include "SolverTypes.h"
#include "Heap.h"
#include <functional>

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
}
