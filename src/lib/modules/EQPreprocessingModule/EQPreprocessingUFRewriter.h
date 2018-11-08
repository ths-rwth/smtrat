#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_EQPREPROCESSINGUFREWRITER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_EQPREPROCESSINGUFREWRITER_H_

#include "../../Common.h"

#include <unordered_map>
#include <unordered_set>
#include <set>
#include <vector>

namespace smtrat {
	struct UFRewriter {
		public:
			typedef carl::UVariable UVariable;
			typedef carl::UFInstance UFInstance;
			typedef carl::UninterpretedFunction UFunction;
			typedef carl::UTerm UTerm;
			typedef carl::UEquality UEquality;

			FormulaT rewrite_ueq(const FormulaT& formula) {
				assert(formula.getType() == carl::UEQ);

				const UEquality& ueq = formula.uequality();
				UVariable lhs, rhs;
				bool changed = false;

				if(ueq.lhs().isUFInstance()) {
					changed = true;
					lhs = P_handle_UF(ueq.lhs().asUFInstance());
				} else {
					lhs = ueq.lhs().asUVariable();
				}

				if(ueq.rhs().isUFInstance()) {
					changed = true;
					rhs = P_handle_UF(ueq.rhs().asUFInstance());
				} else {
					rhs = ueq.rhs().asUVariable();
				}

				return changed ? FormulaT(UTerm(lhs), UTerm(rhs), ueq.negated()) : formula;
			}

			const FormulaSetT& congruences() const noexcept { return mCongruences; }

			const std::unordered_map<UFInstance, UVariable>& UFItoVar() const noexcept { return mUFIToVar; }

		private:
			UVariable P_handle_UF(const UFInstance& instance) {
				auto iter = mUFIToVar.find(instance);

				if(iter == mUFIToVar.end()) {
					const UFunction& fn = instance.uninterpretedFunction();

					iter = mUFIToVar.emplace(instance, UVariable(carl::freshUninterpretedVariable(), fn.codomain())).first;
					mVarToUFI.emplace(iter->second, iter->first);

					auto fniter = mFnToUFI.find(fn);
					if(fniter == mFnToUFI.end()) {
						fniter = mFnToUFI.emplace(fn, std::vector<UFInstance>()).first;
					} else {
						const std::vector<UTerm>& iargs = instance.args();

						for(const UFInstance& other : fniter->second) {
							FormulaSetT disj;
							const std::vector<UTerm>& oargs = other.args();

							disj.emplace(FormulaT(UTerm(iter->second), UTerm(mUFIToVar.find(other)->second), false));
							for(std::size_t i = 0; i < iargs.size(); ++i) {
								if(!(iargs[i] == oargs[i])) {
									disj.emplace(carl::NOT, FormulaT(UTerm(iargs[i]), UTerm(oargs[i]), false));
								}
							}

							FormulaT disj_(carl::OR, std::move(disj));
							mCongruences.insert(disj_);
						}
					}

					fniter->second.push_back(instance);
				}

				return iter->second;
			}

			// mapping of function instances to variables and back
			std::unordered_map<UFunction, std::vector<UFInstance>> mFnToUFI;
			std::unordered_map<UFInstance, UVariable> mUFIToVar;
			std::unordered_map<UVariable, UFInstance> mVarToUFI;

			// additional formulas (without origins) for functional congruence
			FormulaSetT mCongruences;
	};
}

#endif
