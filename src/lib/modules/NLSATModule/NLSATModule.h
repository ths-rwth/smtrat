/**
 * @file NLSATModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-08-08
 * Created on 2016-08-08.
 */

#pragma once

#include "../../solver/Module.h"
#include "NLSATStatistics.h"
#include "NLSATSettings.h"

#include "AssignmentGenerator.h"
#include "ExplanationGenerator.h"
#include "LemmaBuilder.h"

namespace smtrat
{
	template<typename Settings>
	class NLSATModule : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			NLSATStatistics mStatistics;
#endif
			
			std::vector<std::pair<carl::Variable,FormulaT>> mAssignedVariables;
			Model mAssignedModel;
			carl::Variable mCurrentVariable = carl::Variable::NO_VARIABLE;
			
			AssignmentGenerator mAssignmentGenerator;
			
			std::vector<carl::Variable> getOrderedVariables() const {
				std::vector<carl::Variable> vars;
				for (const auto& var: mAssignedVariables) {
					vars.push_back(var.first);
				}
				vars.push_back(mCurrentVariable);
				std::reverse(vars.begin(), vars.end());
				return vars;
			}
			
			bool isVCAssignmentValid(const VariableComparisonT& vc) const {
				Model m = mAssignedModel;
				m.assign(vc.var(), vc.value());
				SMTRAT_LOG_TRACE("smtrat.nlsat", m);
				auto res = m.evaluated(vc.var());
				SMTRAT_LOG_TRACE("smtrat.nlsat", vc << " -> " << res);
				return res.isRational() || res.isRAN();
			}
			
			carl::Variable getVariable() const {
				SMTRAT_LOG_TRACE("smtrat.nlsat", "Getting variable");
				carl::Variables vars;
				for (const auto& c: rReceivedFormula()) {
					c.formula().arithmeticVars(vars);
					SMTRAT_LOG_TRACE("smtrat.nlsat", c.formula() << " -> " << vars);
				}
				for (const auto& v: mAssignedVariables) {
					vars.erase(v.first);
				}
				if (vars.size() > 1) std::exit(81);
				assert(vars.size() <= 1);
				if (vars.empty()) return carl::Variable::NO_VARIABLE;
				SMTRAT_LOG_DEBUG("smtrat.nlsat", "Variable is " << *vars.begin());
				return *vars.begin();
			}
			
			void explain(const FormulasT& reason, const FormulaT& implication) {
				ExplanationGenerator eg(reason, getOrderedVariables(), mAssignedModel);
				NLSATLemmaBuilder lb(mAssignedVariables, implication, eg);
				lb.generateLemmas([this](const auto& f){ addLemma(f); }, NLSATLemmaStrategy::ORIGINAL);
				//lb.generateLemmas([this](const auto& f){}, NLSATLemmaStrategy::NEW);
			}
			bool checkAgainstFullModel() {
				for (const auto& f: rReceivedFormula()) {
					auto res = carl::model::evaluate(f.formula(), mAssignedModel);
					if (res.isBool() && !res.asBool()) {
						SMTRAT_LOG_DEBUG("smtrat.nlsat", "Model does not satisfy " << f.formula());
						carl::Variables vars;
						f.formula().arithmeticVars(vars);
						FormulasT core;
						//for (const auto& v: mAssignedVariables) {
						//	if (vars.find(v.first) != vars.end()) {
						//		core.emplace_back(v.second);
						//	}
						//}
						core.emplace_back(f.formula());
						explain(core, f.formula().negated());
						return false;
					}
				}
				return true;
			}

		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			NLSATModule(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~NLSATModule();
			
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
	};
}
