#pragma once

#include "../../../datastructures/mcsat/nlsat.h"
#include "../../../datastructures/mcsat/nlsat/NLSAT.h"

#include <carl/util/tuple_util.h>

namespace smtrat {
namespace mcsat {
    
    template<typename Settings>
    class MCSATBackend {
        typename Settings::BackendType mBackend;
        
        public:
        
            // TODO
        friend std::ostream& operator<<(std::ostream& os, const MCSATBackend<Settings>& backend);
        
        void pushConstraint(const FormulaT& f) {
            mBackend.pushConstraint(f);
	}
    
        void popConstraint(const FormulaT& f) {
            mBackend.popConstraint(f);
        }
        
        void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
            mBackend.pushAssignment(v, mv, f);
        }
        
        void popAssignment(carl::Variable v) {
            mBackend.popAssignment(v);
        }
        
        const auto& getModel() const {
            return mBackend.getModel();
	}
        
        auto findAssignment(carl::Variable var) const { //AssignmentFinder::AssignmentOrConflict
            return mBackend.findAssignment(var);
        }
        
        boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f) {
            return mBackend.isInfeasible(var, f);
        }
        
        FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication) {
            return mBackend.explain(var, reason, implication);
        }
        
    };
    
    
    template<typename... Backends>
    class MultiBackend {
            

            public:
                
            using B = std::tuple<Backends...>;
            B mBackends;
                
            //friend std::ostream& operator<<(std::ostream& os, const MultiBackend<Backends...>& backend);
            
            void pushConstraint(const FormulaT& f) {
                    carl::tuple_foreach( 
                            [f](auto& b){ b.pushConstraint(f); return true; },
                            mBackends
                    );
            }

            void popConstraint(const FormulaT& f) {
                    carl::tuple_foreach(
                            [f](auto& b){ b.popConstraint(f); return true; },
                            mBackends
                    );
            }

            void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
                    carl::tuple_foreach(
                            [v,mv,f](auto& b){ b.pushAssignment(v, mv, f); return true; },
                            mBackends
                    );
            }

            void popAssignment(carl::Variable v) {
                    carl::tuple_foreach(
                            [v](auto& b){ b.popAssignment(v); return true; },
                            mBackends
                    );
            }

            const auto& getModel() const {
                    auto models = carl::tuple_foreach(
                            [](const auto& b){ return b.getModel(); },
                            mBackends
                    );
                    return std::get<0>(models); //TODO was mit den anderen? 
            }

            auto findAssignment(carl::Variable var) const { //AssignmentFinder::AssignmentOrConflict
                    auto assignments = carl::tuple_foreach(
                            [var](const auto& b){ return b.findAssignment(var); },
                            mBackends
                    );
                    return std::get<0>(assignments); //TODO was mit den anderen? 
            }

            boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f) {
                    auto infeasible = carl::tuple_foreach(
                            [var,f](auto& b){ return b.isInfeasible(var, f); },
                            mBackends
                    );
                    return std::get<0>(infeasible); //TODO was mit den anderen? 
            }

            FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication) {
                    auto expl = carl::tuple_foreach(
                            [var,reason,implication](auto& b){ return b.explain(var, reason, implication); },
                            mBackends
                    );
                    return std::get<0>(expl); //TODO was mit den anderen? 
            }
           
    };

    struct BackendSettings1
    {
        using BackendType = nlsat::NLSAT;
	//typedef nlsat::NLSAT BackendType;
    };
    
    //TODO
    inline std::ostream& operator<<(std::ostream& os, const MCSATBackend<BackendSettings1>& backend) {
            return operator<<(os, backend.mBackend);
    } 
    
    struct MultiBackendSettings1
    {
        using BackendType = MultiBackend<nlsat::NLSAT>;
	//typedef MultiBackend<nlsat::NLSAT> BackendType;
    };
    

    /*inline std::ostream& operator<<(std::ostream& os, const MultiBackend<nlsat::NLSAT>& backends) {
            auto output = carl::tuple_foreach(
                    [&os](const auto& b){ return operator<<(os, b); },
                    backends.mBackends
            ); 
            return std::get<0>(output);
    } */
    
    inline std::ostream& operator<<(std::ostream& os, const MCSATBackend<MultiBackendSettings1>& backend) {
            return operator<<(os, std::get<0>(backend.mBackend.mBackends));
    } 
    
}
}


