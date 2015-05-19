#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_BOOLUEQREWRITER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_BOOLUEQREWRITER_H_

#include "FormulaVisitor.hpp"
#include "../../Common.h"

namespace smtrat {
	struct CollectBoolsInUEQs : public formula_visitor<CollectBoolsInUEQs, void> {
		public:
			void visit_ueq(const FormulaT& formula) {
				const carl::UEquality& ueq = formula.uequality();
				P_handle_arg(ueq.lhs(), ueq.lhsIsUF());
				P_handle_arg(ueq.rhs(), ueq.rhsIsUF());
			}

			CollectBoolsInUEQs(const CollectBoolsInUEQs&) = delete;
			CollectBoolsInUEQs& operator=(const CollectBoolsInUEQs&) = delete;

			CollectBoolsInUEQs() = default;
			CollectBoolsInUEQs(CollectBoolsInUEQs&&) = default;
			CollectBoolsInUEQs &operator=(CollectBoolsInUEQs&&) = default;

			bool foundBoolInUEQ() { return !mBools.empty(); }

		private:
			void P_handle_arg(const carl::UEquality::Arg& arg, bool isUF) {
				static const carl::Sort BOOL_SORT = carl::SortManager::getInstance().getInterpreted(carl::VariableType::VT_BOOL);

				if(isUF) {
					for(const carl::UVariable& var : boost::get<carl::UFInstance>(arg).args()) {
						if(var.domain() == BOOL_SORT) {
							mBools.emplace(var());
						}
					}
				} else {
					const carl::UVariable &var = boost::get<carl::UVariable>(arg);
					if(var.domain() == BOOL_SORT) {
						mBools.emplace(var());
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
				mHelperIneq(FormulaT(carl::NOT, FormulaT(mTrueHelper, mFalseHelper, false)))
			{}

			void setCollected(CollectBoolsInUEQs&& collected) {
				mCollected = std::move(collected);
			}

			FormulaT rewrite_bool(const FormulaT& formula) {
				carl::Variable b = formula.boolean();

				if(mCollected.mBools.count(b)) {
					return FormulaT(carl::UVariable(b), mTrueHelper, false);
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
							FormulaT(uvar, mTrueHelper, false),
							FormulaT(uvar, mFalseHelper, false)
						)
					);

					formulaMap.emplace(FormulaT(carl::TRUE),
						FormulaT(
							carl::OR,
							FormulaT(carl::NOT, FormulaT(uvar, mTrueHelper, false)),
							FormulaT(carl::NOT, FormulaT(uvar, mFalseHelper, false))
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
