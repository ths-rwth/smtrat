#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_ORPATHSHORTENER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_ORPATHSHORTENER_H_

#include "FormulaVisitor.hpp"
#include "ModuleWrapper.h"
#include "../EQModule/VariantHash.h"
#include "../EQModule/pmatrix.hpp"

namespace smtrat {
	/**
	 * A rewriter that checks every (X)OR that only contains ANDs and UEQs
	 * as children for equalities that hold for every alternative, and
	 * adds such equalities explicitly.
	 * This should run after NNF transformation (but clearly before CNF transformation).
	 * This defeats eq_diamond examples (and also more general cases where
	 * the paths are longer or irregular).
	 */
	struct OrPathShortener {
		public:
			OrPathShortener(ModuleWrapper<EQModule<EQSettingsForPreprocessing>>& facts) :
				mFacts(facts)
			{}

			FormulaT rewrite_or(const FormulaT& formula, FormulaSetT&& subformulas) {
				return P_do_rewrite(formula, std::move(subformulas));
			}

			FormulaT rewrite_xor(const FormulaT& formula, FormulasMultiT&& subformulas) {
				return P_do_rewrite(formula, std::move(subformulas));
			}

			void enter_default(const FormulaT& formula) {
				mStack.push_back(formula);
			}

			FormulaT rewrite_default(const FormulaT& formula, const FormulaT& default_result) {
				assert(!mStack.empty() && formula == mStack.back());
				mStack.pop_back();
				return default_result;
			}

		private:
			typedef carl::UVariable UVariable;
			typedef carl::UFInstance UFInstance;
			typedef carl::UninterpretedFunction UFunction;
			typedef carl::UEquality UEquality;
			typedef carl::UTerm UArg;

			struct eqentry {
				eqentry() :
					cnt(0)
				{}

				std::size_t cnt;
			};

			typedef std::unordered_map<UArg, std::size_t> var_index;
			typedef var_index::iterator v_iterator;
			typedef pmatrix<eqentry> pair_map;

			void handleEQ(const FormulaT& formula, var_index& vars, std::size_t& size) {
				assert(formula.getType() == carl::UEQ && !formula.uequality().negated());

				const UArg &lhs(formula.uequality().lhs()), &rhs(formula.uequality().rhs());
				if(!(lhs == rhs)) {
					v_iterator iter;
					bool inserted;

					std::tie(iter, inserted) = vars.emplace(lhs, size);
					if(inserted) {
						++size;
					}

					std::tie(iter, inserted) = vars.emplace(rhs, size);
					if(inserted) {
						++size;
					}

					if(!mFacts.isAsserted(formula)) {
						mFacts.add(formula);
						mAsserted.push_back(formula);
					}
				}
			}

			template<template<typename FormulaType, typename Compare, typename Allocator> class SetType, typename Compare, typename Allocator>
				FormulaT P_do_rewrite(const FormulaT& origFormula, SetType<FormulaT, Compare, Allocator>&& subformulas)
			{
				assert(!mStack.empty() && origFormula == mStack.back());
				mStack.pop_back();

				for(const FormulaT& f : subformulas) {
					if(f.getType() != carl::AND && f.getType() != carl::UEQ) {
						return FormulaT(origFormula.getType(), std::move(subformulas));
					}
				}

				var_index varIndex;
				std::size_t size = 0;
				pair_map pairMap;

				for(const FormulaT& f : subformulas) {
					if(f.getType() == carl::AND) {
						for(const FormulaT& sf : f.subformulas()) {
							if(sf.getType() == carl::UEQ) {
								handleEQ(sf, varIndex, size);
							}
						}
					} else {
						handleEQ(f, varIndex, size);
					}

					mFacts.get().process_merge_lists();

					for(auto i = varIndex.begin(), e = varIndex.end(); i != e; ++i) {
						auto j = i; ++j;
						for(; j != e; ++j) {
							if(mFacts.get().get_class(i->first) == mFacts.get().get_class(j->first)) {
								++pairMap.at(std::min(i->second, j->second), std::max(i->second, j->second)).cnt;
							}
						}
					}

					for(FormulaT& f : mAsserted) {
						mFacts.remove(f);
					}
					mAsserted.clear();
				}

				FormulaSetT addFormulas;
				for(auto i = varIndex.begin(), e = varIndex.end(); i != e; ++i) {
					auto j = i; ++j;
					for(; j != e; ++j) {
						if(pairMap.at(std::min(i->second, j->second), std::max(i->second, j->second)).cnt == subformulas.size()) {
							FormulaT eq(i->first, j->first, false);
							const FormulasT& sub = mStack.back().subformulas();
							if(mStack.empty() || mStack.back().getType() != carl::AND || !std::count(sub.begin(), sub.end(), eq)) {
								addFormulas.insert(eq);
							}
						}
					}
				}

				if(addFormulas.empty()) {
					return FormulaT(origFormula.getType(), std::move(subformulas));
				} else {
					addFormulas.insert(FormulaT(origFormula.getType(), std::move(subformulas)));
					return FormulaT(carl::AND, std::move(addFormulas));
				}
			}

			ModuleWrapper<EQModule<EQSettingsForPreprocessing>>& mFacts;
			std::vector<FormulaT> mStack;
			std::vector<FormulaT> mAsserted;
	};
}

#endif /* SRC_LIB_MODULES_EQPREPROCESSINGMODULE_ORPATHSHORTENER_H_ */
