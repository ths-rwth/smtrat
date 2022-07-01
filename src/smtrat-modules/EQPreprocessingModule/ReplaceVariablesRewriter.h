#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_REPLACEVARIABLESREWRITER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_REPLACEVARIABLESREWRITER_H_

#include "ModuleWrapper.h"
#include "FormulaVisitor.hpp"
#include <smtrat-common/smtrat-common.h>
#include "../EQModule/EQModule.h"

namespace smtrat {
	struct ReplaceVariablesRewriter {
		public:
			typedef carl::UTerm term_type;
			typedef carl::UEquality UEquality;
			typedef carl::UVariable UVariable;
			typedef carl::UninterpretedFunction UninterpretedFunction;
			typedef carl::UFInstance UFInstance;

			ReplaceVariablesRewriter(std::unordered_map<FormulaT, bool>& facts, ModuleWrapper<EQModule<EQSettingsForPreprocessing>>& helper) :
				mEQHelper(helper),
				mFacts(facts),
				mDepth(0),
				mNeedMerge(false)
			{}

			FormulaT rewrite_ueq(const FormulaT& ueq) {
				--mDepth;

				if(
					!mFacts.count(ueq) && (
					!mEQHelper.isAsserted(ueq) ||
					mDepths.empty() ||
					mDepth > mDepths.back() ||
					std::find(mAssertions.back().begin(), mAssertions.back().end(), ueq) == mAssertions.back().end()
				)) {
					if(mNeedMerge) {
						mEQHelper.get().process_merge_lists();
						mNeedMerge = false;
					}

					const term_type &lhs = ueq.u_equality().lhs();
					const term_type &rhs = ueq.u_equality().rhs();

					const term_type *rep_lhs = mEQHelper.get().find_representative(lhs);
					const term_type *rep_rhs = mEQHelper.get().find_representative(rhs);

					if(rep_lhs == nullptr) {
						rep_lhs = &lhs;
					}

					if(rep_rhs == nullptr) {
						rep_rhs = &rhs;
					}

					if(!(lhs == *rep_lhs) || !(rhs == *rep_rhs)) {
						return FormulaT(*rep_lhs, *rep_rhs, false);
					}
				}

				return ueq;
			}

			void enter_default(const FormulaT&) {
				++mDepth;
			}

			FormulaT rewrite_default(const FormulaT&, const FormulaT& result) {
				--mDepth;
				return result;
			}

			void enter_and(const FormulaT& /*formula*/) {
				++mDepth;
//				mDepths.push_back(++mDepth);
//				mAssertions.emplace_back();
//
//				for(const FormulaT& subformula : formula.subformulas()) {
//					if(subformula.type() == carl::UEQ) {
//						if(!mEQHelper.isAsserted(subformula)) {
//							mEQHelper.assertSubformula(subformula);
//							mAssertions.back().push_back(subformula);
//							mNeedMerge = true;
//						}
//					}
//				}
			}

			FormulaT rewrite_and(const FormulaT&/* formula*/, FormulaSetT&& subformulas) {
//				for(const FormulaT& asserted : mAssertions.back()) {
//					mEQHelper.removeSubformula(asserted);
//				}
//				mAssertions.pop_back();
//				mDepths.pop_back();

				--mDepth;
				return FormulaT(carl::AND, std::move(subformulas));
			}

		private:
			ModuleWrapper<EQModule<EQSettingsForPreprocessing>>& mEQHelper;
			std::unordered_map<FormulaT, bool> &mFacts;
			std::vector<std::vector<FormulaT>> mAssertions;
			std::vector<std::size_t> mDepths;
			std::size_t mDepth;
			bool mNeedMerge;
	};
}

#endif
