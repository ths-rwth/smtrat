/**
 * @file EQPreprocessingModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-12-05
 * Created on 2014-12-05.
 */

#include "EQPreprocessingModule.h"
#include <carl/formula/model/uninterpreted/SortValueManager.h>

namespace smtrat
{
	/**
	 * Constructors.
	 */
	template<class Settings>
		EQPreprocessingModule<Settings>::EQPreprocessingModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager) :
			Module(_formula, _conditionals, _manager),
			mEQHelper(),
			mBoolRewriter(nullptr)
	{}

	/**
	 * Destructor.
	 */
	template<class Settings>
		EQPreprocessingModule<Settings>::~EQPreprocessingModule()
	{
		delete mBoolRewriter;
	}

	template<class Settings>
		void EQPreprocessingModule<Settings>::P_rewrite_congruences()
	{
		if(Settings::rewriteFunctionInstances) {
			for(old_to_new_iter i = mOldToNew.begin(), e = mOldToNew.end(); i != e; ++i) {
				i->second = mRewriter.apply(i->second);
			}

#ifdef SMTRAT_DEVOPTION_Statistics
			mStatistics.countCongruencesAdded(mRewriter.get().congruences().size());
#endif

			for(const FormulaT& cong : mRewriter.get().congruences()) {
				mOldToNew.emplace(FormulaT(carl::TRUE), cong);
			}
		}
	}

	template<class Settings> template<typename Rewriter, typename... Args>
		bool EQPreprocessingModule<Settings>::apply_rewriting(Args&&... args)
	{
		bool changed = false;

		for(old_to_new_iter i = mOldToNew.begin(), e = mOldToNew.end(); i != e; ++i) {
			changed |= apply_to_formula<Rewriter>(i, std::forward<Args>(args)...);
		}

		return changed;
	}

	template<class Settings> template<typename Rewriter, typename... Args>
		bool EQPreprocessingModule<Settings>::apply_to_formula(old_to_new_iter formula, Args&&... args)
	{
		bool changed = false;

		formula_rewriter<Rewriter> rewriter(std::forward<Args>(args)...);
		FormulaT result(rewriter.apply(formula->second));

		if(!(result == formula->second)) {
			changed = true;
			formula->second = result;
		}

		return changed;
	}

	template<class Settings>
		void EQPreprocessingModule<Settings>::P_NNF_transform()
	{
		if(Settings::performNNF || Settings::rewriteBooleanDomainConstraints) {
			apply_rewriting<NNFPreparation>();
			apply_rewriting<NNFRewriter>();
			apply_rewriting<JunctorMerger>();
		}
	}

	template<class Settings>
		void EQPreprocessingModule<Settings>::P_rewrite_bool_domain()
	{
		if(Settings::rewriteBooleanDomainConstraints) {
			CollectBoolsInUEQs collector;

			for(old_to_new_iter i = mOldToNew.begin(), e = mOldToNew.end(); i != e; ++i) {
				collector.apply(i->second);
			}

			if(collector.foundBoolInUEQ()) {
				if(mBoolRewriter == nullptr) {
					mBoolRewriter = new formula_rewriter<BoolUEQRewriter>(std::move(collector));
				} else {
					mBoolRewriter->get().setCollected(std::move(collector));
				}

				for(old_to_new_iter i = mOldToNew.begin(), e = mOldToNew.end(); i != e; ++i) {
					i->second = mBoolRewriter->apply(i->second);
				}

				mBoolRewriter->get().addFormulas(mOldToNew);
				mBoolRewriter->get().addDomainConstraints(mOldToNew);
			}
		}
	}

	template<class Settings>
		std::pair<bool,bool> EQPreprocessingModule<Settings>::P_collect_fact(const FormulaT& origin, const FormulaT& fact, bool negated)
	{
		std::unordered_map<FormulaT, bool>::iterator iter;
		bool inserted;

		std::tie(iter, inserted) = mFacts.emplace(fact, !negated);
		if(inserted) {
			FormulaT realFact(fact.uequality().lhs(), fact.uequality().rhs(), negated);
			mFactOrigins.emplace(realFact, origin);
			return std::make_pair(mEQHelper.add(realFact), false);
		} else {
			if(negated == iter->second) {
				FormulaT realFact(fact.uequality().lhs(), fact.uequality().rhs(), negated);
				mFactOrigins.emplace(realFact, origin);
				bool result = mEQHelper.add(realFact);
				assert(!result); (void)result;
				return std::make_pair(false, false);
			}
		}

		return std::make_pair(true, true);
	}

	template<class Settings>
		std::pair<bool,bool> EQPreprocessingModule<Settings>::P_collect_facts()
	{
		bool stable = true;

		for(auto&& value : mOldToNew) {
			if(value.second.getType() == carl::UEQ) {
				std::pair<bool,bool> r = P_collect_fact(value.first, value.second, false);
				if(!r.first) {
					return std::make_pair(false,false);
				}

				stable &= r.second;
			} else if(value.second.getType() == carl::NOT && value.second.subformula().getType() == carl::UEQ) {
				std::pair<bool,bool> r = P_collect_fact(value.first, value.second.subformula(), true);
				if(!r.first) {
					return std::make_pair(false,false);
				}

				stable &= r.second;
			} else if(value.second.getType() == carl::AND) {
				for(const FormulaT& fact : value.second.subformulas()) {
					if(fact.getType() == carl::UEQ) {
						std::pair<bool,bool> r = P_collect_fact(value.first, fact, false);
						if(!r.first) {
							return std::make_pair(false,false);
						}

						stable &= r.second;
					} else if(fact.getType() == carl::NOT && fact.subformula().getType() == carl::UEQ) {
						std::pair<bool,bool> r = P_collect_fact(value.first, fact.subformula(), true);
						if(!r.first) {
							return std::make_pair(false,false);
						}

						stable &= r.second;
					}
				}
			}
		}

		return std::make_pair(mEQHelper.check(), stable);
	}

	template<class Settings>
		void EQPreprocessingModule<Settings>::P_do_preprocessing()
	{
		for(auto&& formula : rReceivedFormula()) {
			mOldToNew.emplace(formula.formula(), formula.formula());
		}

		P_NNF_transform();
		P_rewrite_bool_domain();
		P_rewrite_congruences();
	}

	template<class Settings>
		Answer EQPreprocessingModule<Settings>::checkCore()
	{
		if(Settings::printFormulas) {
			for(auto&& f : rReceivedFormula()) {
				std::cout << f.formula() << std::endl;
			}
		}

		// run the actual pre-processing that is independent of fact collection
		P_do_preprocessing();

		bool changed;

		do {
			bool consistent, stable;
			std::tie(consistent, stable) = P_collect_facts();

			// collect facts (literals that are always true/false)
			if(!consistent) {
				// The formula is unsat; use the infeasible subset from the helper module
				assert(mEQHelper.infeasibleSubsets().size() == 1);
				//const FormulaSetT& infeasible = mEQHelper.infeasibleSubsets().front();
				FormulaSetT constructInfeasible;

				/*
				for(const FormulaT& formula : infeasible) {
					assert(mFactOrigins.count(formula));
					const FormulaT& orig = mFactOrigins.find(formula)->second;

					if(orig.getType() != carl::TRUE) {
						constructInfeasible.insert(orig);
					}
				}
				std::cout << "Infeasible after conversion: " << constructInfeasible << std::endl;
				*/
				for (const auto& f: rReceivedFormula()) {
					constructInfeasible.insert(f.formula());
				}

				mInfeasibleSubsets.emplace_back(std::move(constructInfeasible));
				return UNSAT;
			}

			changed = !stable;
			if(apply_rewriting<OrPathShortener>(mEQHelper)) {
				changed = true;
				apply_rewriting<JunctorMerger>();
			}

			if(Settings::rewriteUsingFacts) {
				if(apply_rewriting<ReplaceVariablesRewriter>(mFacts, mEQHelper)) {
					changed = true;
					apply_rewriting<JunctorMerger>();
				}
			}
		} while(changed);

		// go through the output of the pre-processing and pass it on
		for(ModuleInput::const_iterator i = rReceivedFormula().begin(), e = rReceivedFormula().end(); i != e; ++i) {
			if(!(i->formula() == FormulaT(carl::TRUE))) {
				old_to_new_iter f = mOldToNew.find(i->formula());

				if(f == mOldToNew.end() || f->first == f->second) {
					addReceivedSubformulaToPassedFormula(i);
				} else {
					if(!(f->first == FormulaT(carl::TRUE))) {
						addSubformulaToPassedFormula(f->second, f->first);
					}
				}
			}
		}

		old_to_new_iter abegin, aend;

		for(std::tie(abegin, aend) = mOldToNew.equal_range(FormulaT(carl::TRUE)); abegin != aend; ++abegin) {
			addSubformulaToPassedFormula(abegin->second);
		}

		if(Settings::printFormulas) {
			std::cout << "Passed formula: " << std::endl;
			for(auto&& f : rPassedFormula()) {
				std::cout << f.formula() << std::endl;
			}
		}

		// Call backends.
		Answer answer = runBackends();
		if(answer == UNSAT) {
			getInfeasibleSubsets();
		}

		return answer;
	}

	template<typename Settings>
		void EQPreprocessingModule<Settings>::P_update_model()
	{
		clearModel();

		if(solverState() == SAT) {
			getBackendsModel();

			if(Settings::rewriteFunctionInstances) {
				for(auto&& pair : mRewriter.get().UFItoVar()) {
					const UFInstance& instance = pair.first;
					const UVariable& helper = pair.second;

					carl::UFModel &ufModel = mModel.emplace(instance.uninterpretedFunction(), carl::UFModel(instance.uninterpretedFunction())).first->second.asUFModel();

					std::vector<carl::SortValue> args;
					args.reserve(instance.args().size());
					for(std::size_t i = 0, s = instance.args().size(); i < s; ++i) {
						assert(instance.args()[i].isUVariable());
						const UVariable& var = instance.args()[i].asUVariable();
						auto model_iter = mModel.find(var.variable());
						
						if(model_iter == mModel.end()) {
							// there is no model value for the variable, because it does not occur outside of function instances.
							// this should really look different in the module (like not including the index at all), but we can just assume that all the values are distinct.
							args.push_back(newSortValue(var.domain()));
						} else {
							// use the model value of the variable
							args.push_back(model_iter->second.asSortValue());
						}
					}

					auto modelItr = mModel.find(helper.variable());
					assert(modelItr != mModel.end());
					ufModel.extend(std::move(args), modelItr->second.asSortValue());
					mModel.erase(modelItr);
				}
			}
		}
	}

	template<typename Settings>
		void EQPreprocessingModule<Settings>::updateModel() const
	{
		const_cast<EQPreprocessingModule<Settings>&>(*this).P_update_model();
	}
}

#include "Instantiation.h"
