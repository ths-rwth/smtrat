#pragma once

#include <vector>

#include "common.h"
#include "projection/Projection.h"
#include "utils/CADConstraints.h"
#include "utils/CADCoreIntervalBased.h"
#include "utils/ConflictGraph.h"
#include "utils/MISGeneration.h"
#include "debug/TikzHistoryPrinter.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class CADIntervalBased {
	public:
		template<CoreIntervalBasedHeuristic CH>
		friend struct CADCoreIntervalBased;
		using SettingsT = Settings;
	private:
		std::vector<carl::Variable> mVariables;			/**< variables in given order */
		std::vector<ConstraintT> mConstraints;			/**< constraints */
		FormulaSetT mLastUnsatCover;					/**< stores last unsat cover */

	public:
		CADIntervalBased():
			mConstraints() {}
		~CADIntervalBased() {}

		std::size_t dim() const {
			return mVariables.size();
		}
		const auto& getVariables() const {
			return mVariables;
		}
		const auto& getConstraints() const {
			return mConstraints;
		}
		const auto& getLastUnsatCover() const {
			return mLastUnsatCover;
		}
		void setUnsatCover(const FormulaSetT& cover) {
			mLastUnsatCover = cover;
		}

		/** @returns depth of var iff var is in var list, else 0 */
		std::size_t getDepthOfVar(carl::Variable var) {
			for(std::size_t i = 0; i < mVariables.size(); i++) {
				if(var == mVariables.at(i))
					return i+1;
			}
			return 0;
		}

		/** @brief gets the next variable in the order 
		 * 
		 * @note if the var is the last one, it is returned
		 * @note if the given var is not in the list, the first one in the list is returned
		 * 
		 * @returns next variable in var order
		 */
		carl::Variable getNextVar(
			carl::Variable var	/**< get var after this one */
		) {
			for(size_t i = 0; i < mVariables.size(); i++) {
				// case var is last one in order
				if(var == mVariables.back())
					return var;
				// case var is found in order & is not last one in order
				if(var == mVariables.at(i))
					return mVariables.at(i+1);
			}
			// if var was not found, return first one in order
			return mVariables.at(0);
		}

		void reset(const std::vector<carl::Variable>& vars) {
			mVariables = vars;
			mConstraints.clear();
		}

		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			mConstraints.push_back(c);
		}

		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			for(auto it = mConstraints.begin(); it != mConstraints.end(); it++) {
				if(*(it) == c) {
					mConstraints.erase(it);
					break;
				}
			}
		}
		
		Answer check(Assignment& assignment) {

			CADCoreIntervalBased<Settings::coreHeuristic> cad;
			auto res = cad(assignment, *this);
			
			return res;
		}
		
	};
}
}
