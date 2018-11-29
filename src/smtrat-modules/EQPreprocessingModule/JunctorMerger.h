#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_JUNCTORMERGER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_JUNCTORMERGER_H_

#include <smtrat-common/smtrat-common.h>
#include "FormulaVisitor.hpp"

namespace smtrat {
	struct JunctorMerger {
		public:
			FormulaT rewrite_or (const FormulaT& formula, FormulaSetT&& subformulas) {
				return P_merge(formula.getType(), std::move(subformulas));
			}

			FormulaT rewrite_and(const FormulaT& formula, FormulaSetT&& subformulas) {
				return P_merge(formula.getType(), std::move(subformulas));
			}

			FormulaT rewrite_xor(const FormulaT& formula, FormulasMultiT&& subformulas) {
				return P_merge(formula.getType(), std::move(subformulas));
			}

		private:
			template<template<typename, typename, typename> class SetType, typename C, typename A>
				FormulaT P_merge(const carl::FormulaType type, SetType<FormulaT, C, A>&& subformulas)
			{
				SetType<FormulaT, C, A> replacements;
				bool changed = false;

				for(auto i = subformulas.begin(); i != subformulas.end(); ) {
					if(i->getType() == type) {
						changed = true;
						std::copy(i->subformulas().begin(), i->subformulas().end(), std::inserter(replacements, replacements.end()));
						subformulas.erase(i++);
					} else {
						++i;
					}
				}

				if(changed) {
					std::move(subformulas.begin(), subformulas.end(), std::inserter(replacements, replacements.end()));
					return FormulaT(type, std::move(replacements));
				} else {
					return FormulaT(type, std::move(subformulas));
				}
			}
	};
}

#endif /* SRC_LIB_MODULES_EQPREPROCESSINGMODULE_JUNCTORMERGER_H_ */
