#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_BOOLUEQREWRITER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_BOOLUEQREWRITER_H_

#include "FormulaVisitor.hpp"
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
	struct CollectBoolsInUEQs : public formula_visitor<CollectBoolsInUEQs, void> {
		public:
			void visit_ueq(const FormulaT& formula) {
				const carl::UEquality& ueq = formula.uequality();
				P_handle_arg(ueq.lhs(), ueq.lhs().isUFInstance());
				P_handle_arg(ueq.rhs(), ueq.rhs().isUFInstance());
			}

			CollectBoolsInUEQs(const CollectBoolsInUEQs&) = delete;
			CollectBoolsInUEQs& operator=(const CollectBoolsInUEQs&) = delete;

			CollectBoolsInUEQs() = default;
			CollectBoolsInUEQs(CollectBoolsInUEQs&&) = default;
			CollectBoolsInUEQs &operator=(CollectBoolsInUEQs&&) = default;

			bool foundBoolInUEQ() { return !mBools.empty(); }

		private:
			void P_handle_arg(const carl::UTerm& arg, bool isUF) {
				static const carl::Sort BOOL_SORT = carl::SortManager::getInstance().getInterpreted(carl::VariableType::VT_BOOL);

				if(isUF) {
					for(const carl::UTerm& term : arg.asUFInstance().args()) {
						assert(term.isUVariable());
						const auto& var = term.asUVariable();
						if(var.domain() == BOOL_SORT) {
							mBools.emplace(var.variable());
						}
					}
				} else {
					const carl::UVariable &var = arg.asUVariable();
					if(var.domain() == BOOL_SORT) {
						mBools.emplace(var.variable());
					}
				}
			}

			std::unordered_set<carl::Variable> mBools;

			friend struct BoolUEQRewriter;
	};

	struct BoolUEQRewriter {
		public:
			BoolUEQRewriter(CollectBoolsInUEQs&& collected) :
				mCollected(std::move(collected)),
				mTrueHelper(carl::freshBooleanVariable()),
				mFalseHelper(carl::freshBooleanVariable()),
				mHelperIneq(FormulaT(carl::NOT, FormulaT(carl::UTerm(mTrueHelper), carl::UTerm(mFalseHelper), false)))
			{}

			void setCollected(CollectBoolsInUEQs&& collected) {
				mCollected = std::move(collected);
			}

			FormulaT rewrite_bool(const FormulaT& formula) {
				carl::Variable b = formula.boolean();

				if(mCollected.mBools.count(b)) {
					return FormulaT(carl::UTerm(carl::UVariable(b)), carl::UTerm(mTrueHelper), false);
				} else {
					return formula;
				}
			}

			void addFormulas(std::unordered_multimap<FormulaT, FormulaT>& formulaMap) {
				formulaMap.emplace(FormulaT(carl::TRUE), mHelperIneq);
			}

			void addDomainConstraints(std::unordered_multimap<FormulaT, FormulaT>& formulaMap) {
				for(const carl::Variable& var : mCollected.mBools) {
					carl::UVariable uvar(var);

					formulaMap.emplace(FormulaT(carl::TRUE),
						FormulaT(carl::OR,
							{FormulaT(carl::UTerm(uvar), carl::UTerm(mTrueHelper), false),
							FormulaT(carl::UTerm(uvar), carl::UTerm(mFalseHelper), false)}
						)
					);

					formulaMap.emplace(FormulaT(carl::TRUE),
						FormulaT(
							carl::OR,
							{FormulaT(carl::NOT, FormulaT(carl::UTerm(uvar), carl::UTerm(mTrueHelper), false)),
							FormulaT(carl::NOT, FormulaT(carl::UTerm(uvar), carl::UTerm(mFalseHelper), false))}
						)
					);
				}
			}

		private:
			CollectBoolsInUEQs mCollected;
			carl::UVariable mTrueHelper;
			carl::UVariable mFalseHelper;
			FormulaT mHelperIneq;
	};
}

#endif /* SRC_LIB_MODULES_EQPREPROCESSINGMODULE_BOOLUEQREWRITER_H_ */
