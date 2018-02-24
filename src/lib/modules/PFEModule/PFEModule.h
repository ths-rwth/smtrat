/**
 * Removes factors of polynomials from the formula.
 * 
 * @file PFEModule.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#pragma once

#include "../../solver/PModule.h"
#include "../../datastructures/VariableBounds.h"
#include "PFEStatistics.h"
#include "PFESettings.h"

namespace smtrat
{
    template<typename Settings>
    class PFEModule : public PModule
    {
        private:
            // Members.
            ///
			carl::FormulaVisitor<FormulaT> visitor;
			/// Collection of bounds of all received formulas.
			vb::VariableBounds<FormulaT> varbounds;
			bool boundsChanged = false;
        public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
            PFEModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~PFEModule();

            // Main interfaces.
			bool addCore( ModuleInput::const_iterator );
            
			/**
			 * Checks the received formula for consistency.
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
            Answer checkCore();
            void removeCore( ModuleInput::const_iterator );
        private:
            
			carl::Relation combine(carl::Relation lhs, carl::Relation rhs, std::size_t exponent) {
				assert(lhs != carl::Relation::NEQ);
				assert(rhs != carl::Relation::NEQ);
				if (rhs == carl::Relation::EQ) return carl::Relation::EQ;
				if (exponent % 2 == 0) {
					if (rhs == carl::Relation::LEQ) rhs = carl::Relation::GEQ;
					else if (rhs == carl::Relation::LESS) rhs = carl::Relation::GREATER;
				}
				switch (lhs) {
					case carl::Relation::GREATER: return rhs;
					case carl::Relation::GEQ: 
						switch (rhs) {
							case carl::Relation::GREATER:
							case carl::Relation::GEQ: return carl::Relation::GEQ;
							case carl::Relation::LEQ:
							case carl::Relation::LESS: return carl::Relation::LEQ;
							default: return carl::Relation::NEQ;
						}
					case carl::Relation::EQ: return carl::Relation::EQ;
					case carl::Relation::LEQ:
						switch (rhs) {
							case carl::Relation::GREATER:
							case carl::Relation::GEQ: return carl::Relation::LEQ;
							case carl::Relation::LEQ:
							case carl::Relation::LESS: return carl::Relation::GEQ;
							default: return carl::Relation::NEQ;
						}
					case carl::Relation::LESS:
						switch (rhs) {
							case carl::Relation::GREATER: return carl::Relation::LESS;
							case carl::Relation::GEQ: return carl::Relation::LEQ;
							case carl::Relation::LEQ: return carl::Relation::GEQ;
							case carl::Relation::LESS: return carl::Relation::GREATER;
							default: return carl::Relation::NEQ;
						}
					case carl::Relation::NEQ: return carl::Relation::NEQ;
				}
				return carl::Relation::NEQ;
			}
			
			Poly getPoly(const std::vector<Factorization::const_iterator>& its) const {
				Poly res = ONE_POLYNOMIAL;
				for (const auto& it: its) res *= carl::pow(it->first, it->second);
				return res;
			}
			
			void generateVariableAssignments() {
				for (const auto& bound: varbounds.getEvalIntervalMap()) {
					if (bound.second.isPointInterval()) {
						FormulasT origins = varbounds.getOriginsOfBounds(bound.first);
						addSubformulaToPassedFormula(FormulaT(bound.first - bound.second.lower(), carl::Relation::EQ), std::make_shared<std::vector<FormulaT>>(std::move(origins)));
					}
				}
			}
			
			EvalRationalIntervalMap completeBounds(const Poly& p) const {
				auto res = varbounds.getEvalIntervalMap();
				for (auto var: p.gatherVariables()) {
					if (res.find(var) == res.end()) {
						res[var] = RationalInterval::unboundedInterval();
					}
				}
				return res;
			}
            
			/**
			 * Removes redundant or obsolete factors of polynomials from the formula.
             */
			FormulaT removeFactors(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeFactorsFunction;
			
			FormulaT removeSquaresFromStrict(const FormulaT& formula);
			FormulaT removeSquares(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeSquaresFunction;
    };
}
