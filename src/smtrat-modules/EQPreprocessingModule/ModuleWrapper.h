#ifndef SRC_LIB_MODULES_EQPREPROCESSINGMODULE_MODULE_WRAPPER_H_
#define SRC_LIB_MODULES_EQPREPROCESSINGMODULE_MODULE_WRAPPER_H_

#include <smtrat-common/smtrat-common.h>
#include <smtrat-solver/Module.h>
#include "../EQModule/EQModule.h"

namespace smtrat {
	template<typename M> class ModuleWrapper {
		public:
			ModuleWrapper() :
				input(),
				module(&input, conditionals, nullptr)
			{}

			M& get() noexcept { return module; }

			bool add(const FormulaT& formula) {
				ModuleInput::iterator iter;
				bool added;

				std::tie(iter, added) = input.add(formula);
				if(added) {
					module.inform(formula);
				}

				asserted.insert(formula);
				return module.add(iter);
			}

			void remove(const FormulaT& formula) {
				ModuleInput::iterator iter = input.find(formula);
				if(iter != input.end()) {
					asserted.erase(formula);
					module.remove(iter);
					input.erase(iter);
				}
			}

			bool isAsserted(const FormulaT& formula) {
				return asserted.count(formula);
			}

			bool check() {
				return module.check() != UNSAT;
			}

			const std::vector<FormulaSetT>& infeasibleSubsets() {
				return module.infeasibleSubsets();
			}

		private:
			FormulaSetT asserted;
			Conditionals conditionals;
			ModuleInput input;
			M module;
	};
}

#endif
