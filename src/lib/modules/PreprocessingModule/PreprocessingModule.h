/**
 * @file   PreprocessingModule.h
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 *
 */

#pragma once

#include "../../solver/PModule.h"
#include "../../datastructures/VariableBounds.h"
#include "PreprocessingSettings.h"

namespace smtrat
{
    /**
     *
     */
	template<typename Settings>
    class PreprocessingModule : public PModule
    {
        private:
			carl::FormulaVisitor<FormulaT> visitor;
		
			/// Bounds that have been added since the last call to isConsistent().
			std::unordered_set<FormulaT> newBounds;
			/// Collection of bounds of all received formulas.
			vb::VariableBounds<FormulaT> varbounds;
			
            std::unordered_map<FormulaT, bool> boolSubs;
            std::map<carl::Variable,Poly> arithSubs;
            
            std::map<carl::Variable,int> mVariablesBounded;
			
			FormulaSetT tmpOrigins;
			void accumulateBoundOrigins(const ConstraintT& constraint) {
				auto tmp = varbounds.getOriginsOfBounds(constraint.variables());
				tmpOrigins.insert(tmp.begin(), tmp.end());
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
			EvalRationalIntervalMap completeBounds(const ConstraintT& c) const {
				auto res = varbounds.getEvalIntervalMap();
				for (auto var: c.variables()) {
					if (res.find(var) == res.end()) {
						res[var] = RationalInterval::unboundedInterval();
					}
				}
				return res;
			}

        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}

            PreprocessingModule( const ModuleInput*, RuntimeSettings*, Conditionals&, Manager* const = nullptr );

            /**
             * Destructor:
             */
            virtual ~PreprocessingModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool addCore( ModuleInput::const_iterator );
            Answer checkCore( bool _full );
            void removeCore( ModuleInput::const_iterator );
			void updateModel() const;

        protected:
			void addBounds(const FormulaT& formula, const FormulaT& _origin);
			void removeBounds(const FormulaT& formula, const FormulaT& _origin);
			
			/**
			 * Removes redundant or obsolete factors of polynomials from the formula.
             */
			FormulaT removeFactors(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeFactorsFunction;
			
			FormulaT eliminateMonomialEquation(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> eliminateMonomialEquationFunction;
			
			/**
			 * Splits the sum-of-squares (sos) decomposition, if the given formula is a constraint with a sos as left-hand side.
             */
			FormulaT splitSOS(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> splitSOSFunction;
			
			/**
			 * Collect the upper and lower bounds of all variables x which only appear as monomial x^i. 
			 */
			void collectUnboundedVars(const FormulaT& formula);
			std::function<void(FormulaT)> collectUnboundedVarsFunction;
			FormulaT removeUnboundedVars(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> removeUnboundedVarsFunction;
			
			/**
			 * Checks if constraints vanish using the variable bounds.
			 */
			FormulaT checkBounds(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> checkBoundsFunction;
			
			/**
			 * Extracts the bounds of a polynomial if it is the only polynomial occurring in a disjunction of constraints.
			 */
			FormulaT extractBounds(const FormulaT& formula);
			std::function<FormulaT(FormulaT)> extractBoundsFunction;
			
			/**
			 * Eliminates all equation forming a substitution of the form x = p with p not containing x.
			 */
			FormulaT elimSubstitutions(const FormulaT& _formula, bool _elimSubstitutions = false );
			
			void enumerateIntegers();
    };

}    // namespace smtrat
