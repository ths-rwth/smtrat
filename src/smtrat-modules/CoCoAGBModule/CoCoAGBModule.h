/**
 * @file CoCoAGBModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-11-29
 * Created on 2017-11-29.
 */

#pragma once

#include <smtrat-solver/Module.h>
#include "CoCoAGBSettings.h"

#include <boost/optional.hpp>
#include <algorithm>

namespace smtrat
{
	template<typename Settings>
	class CoCoAGBModule : public Module
	{
#ifdef USE_COCOA
		struct VariableOrdering {
		private:
			std::vector<carl::Variable> mOrdering;
			
			void addPoly(std::map<carl::Variable, std::size_t>& ordermap, const Poly& p) {
				for (auto var: p.gatherVariables()) {
					auto it = ordermap.find(var);
					if (it == ordermap.end()) {
						ordermap.emplace(var, 1);
					} else {
						it->second++;
					}
				}
			}
			void makeOrdering(const std::map<carl::Variable, std::size_t>& ordermap) {
				std::vector<std::pair<std::size_t, carl::Variable>> flatorder;
				for (const auto& v: ordermap) {
					flatorder.emplace_back(v.second, v.first);
				}
				std::sort(flatorder.begin(), flatorder.end());
				for (const auto& t: flatorder) {
					mOrdering.emplace_back(t.second);
				}
			}
		public:
			VariableOrdering(const std::vector<Poly>& polys) {
				std::map<carl::Variable, std::size_t> ordermap;
				for (const auto& p: polys) addPoly(ordermap, p);
				makeOrdering(ordermap);
			}
			const std::vector<carl::Variable>& getOrdering() const {
				return mOrdering;
			}
		};
		private:
			// Auxiliary variables are needed when transforming inequalities to equalities
			std::map<ConstraintT, carl::Variable> mAuxVariables;
			// Polys constructed from constraints
			std::map<ConstraintT, Poly> mGBPolys;
			
			std::vector<Poly> mLastBasis;
			
			// Create a unique auxiliary variable for every constraint
			carl::Variable getAuxVar(const ConstraintT& c) {
				auto it = mAuxVariables.find(c);
				if (it != mAuxVariables.end()) {
					return it->second;
				}
				return mAuxVariables.emplace(c, carl::freshRealVariable()).first->second;
			}
			// Return the polynomial to be put in the GB, does conversion for inequalities (if enabled)
			boost::optional<Poly> getPoly(const ConstraintT& c) {
				if (c.relation() == carl::Relation::EQ) {
					return c.lhs();
				}
				if (!Settings::convert_inequalities) {
					return boost::none;
				}
				carl::Variable aux = getAuxVar(c);
				switch (c.relation()) {
					case carl::Relation::GEQ:
						return c.lhs() + TermT(-1, aux, 2);
					case carl::Relation::LEQ:
						return c.lhs() + TermT(1, aux, 2);
					case carl::Relation::GREATER:
						return c.lhs() * aux * aux - Rational(1);
					case carl::Relation::LESS:
						return c.lhs() * aux * aux + Rational(1);
					case carl::Relation::NEQ:
						return c.lhs() * aux + Rational(1);
					default:
						assert(false);
						return boost::none;
				}
			}
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			CoCoAGBModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~CoCoAGBModule();
			
			// Main interfaces.
			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore( const FormulaT& _constraint );

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
#endif
	};
}
