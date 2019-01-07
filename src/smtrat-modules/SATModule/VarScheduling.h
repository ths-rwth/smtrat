#pragma once

#include "SolverTypes.h"
#include <functional>

namespace smtrat {
    struct VarSchedulingDefault {
        struct VarOrderLt
        {
            std::function<double(Minisat::Var)> getActivity;

            bool operator ()( Minisat::Var x, Minisat::Var y )
            {
                return getActivity(x) > getActivity(y);
            }

            template<typename BaseModule>
            explicit VarOrderLt( BaseModule& baseModule ):
                getActivity( [&baseModule](Minisat::Var v){ return baseModule.activity[v]; } )
            {}
        };

        struct VarDecidabilityCond
        {
            bool operator ()( Minisat::Var)
            {
                return true;
            }

            template<typename BaseModule>
            explicit VarDecidabilityCond( BaseModule& )
            {}
        };
    };

    template<int maxNumUnassignedVars>
    struct VarSchedulingMcsat {
        struct VarOrderLt
        {
            std::function<double(Minisat::Var)> getActivity;
            std::function<std::size_t(Minisat::Var)> getMaxTheoryLevel;

            bool operator ()( Minisat::Var x, Minisat::Var y )
            {
                auto x_lvl = getMaxTheoryLevel(x);
                auto y_lvl = getMaxTheoryLevel(y);
                return x_lvl < y_lvl || (x_lvl == y_lvl && getActivity(x) > getActivity(y));
            }

            template<typename BaseModule>
            explicit VarOrderLt( BaseModule& baseModule ):
                getActivity( [&baseModule](Minisat::Var v){ return baseModule.activity[v]; } ),
                getMaxTheoryLevel( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxTheoryLevel(v); } )
            {}
        };

        struct VarDecidabilityCond
        {
            std::function<std::size_t(Minisat::Var)> getMaxTheoryLevel;
            std::function<std::size_t()> getLevel;

            bool operator ()( Minisat::Var x)
            {
                static_assert(maxNumUnassignedVars >= 1);
                return getMaxTheoryLevel(x) <= getLevel() + maxNumUnassignedVars;
            }

            template<typename BaseModule>
            explicit VarDecidabilityCond( BaseModule& baseModule ):
                getMaxTheoryLevel( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxTheoryLevel(v); } ),
                getLevel( [&baseModule](){ return baseModule.mMCSAT.level(); } )
            {}
        };
    };

    template<int maxNumUnassignedVars, int maxPreferredDegree>
    struct VarSchedulingMcsatPreferLowDegrees { // TODO test
        
        struct VarOrderLt
        {
            std::function<double(Minisat::Var)> getActivity;
            std::function<std::size_t(Minisat::Var)> getMaxTheoryLevel;
            std::function<std::size_t(Minisat::Var)> getMaxDegree;

            bool operator ()( Minisat::Var x, Minisat::Var y )
            {
                if (getMaxDegree(x) <= maxPreferredDegree && getMaxDegree(y) > maxPreferredDegree) { 
                    return true;
                }

                auto x_lvl = getMaxTheoryLevel(x);
                auto y_lvl = getMaxTheoryLevel(y);
                return x_lvl < y_lvl || (x_lvl == y_lvl && getActivity(x) > getActivity(y));
            }

            template<typename BaseModule>
            explicit VarOrderLt( BaseModule& baseModule ):
                getActivity( [&baseModule](Minisat::Var v){ return baseModule.activity[v]; } ),
                getMaxTheoryLevel( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxTheoryLevel(v); } ),
                getMaxDegree( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxDegree(v); } )
            {}
        };

        struct VarDecidabilityCond
        {
            std::function<std::size_t(Minisat::Var)> getMaxTheoryLevel;
            std::function<std::size_t()> getLevel;
            std::function<std::size_t(Minisat::Var)> getMaxDegree;

            bool operator ()( Minisat::Var x)
            {
                if (getMaxDegree(x) <= maxPreferredDegree) {
                    return true;
                }

                static_assert(maxNumUnassignedVars >= 1);
                return getMaxTheoryLevel(x) <= getLevel() + maxNumUnassignedVars;
            }

            template<typename BaseModule>
            explicit VarDecidabilityCond( BaseModule& baseModule ):
                getMaxTheoryLevel( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxTheoryLevel(v); } ),
                getLevel( [&baseModule](){ return baseModule.mMCSAT.level(); } ),
                getMaxDegree( [&baseModule](Minisat::Var v){ return baseModule.mMCSAT.maxDegree(v); } )
            {}
        };
    };
}
