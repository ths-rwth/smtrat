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

		std::map<ConstraintT, int> mConstraintMap;

		// ProjectionT<Settings> mProjection;
		
		// ID scheme for variables x,y,z:
		// Projection: x=1,y=2,z=3
		// Lifting: x=3,y=2,z=1,anonymous=0
		// std::size_t idPL(std::size_t level) const {
		// 	assert(level > 0 && level <= dim());
		// 	return dim() - level + 1;
		// }
		// std::size_t idLP(std::size_t level) const {
		// 	assert(level > 0 && level <= dim());
		// 	return dim() - level + 1;
		// }

	public:
		debug::TikzHistoryPrinter thp;

		CADIntervalBased():
			mConstraints()
		{
			//@todo add variables?
			
			if (Settings::debugStepsToTikz) {
				thp.configure<debug::TikzTreePrinter>("Lifting");
				thp.configure<debug::TikzDAGPrinter>("Projection");
			}
		}
		~CADIntervalBased() {
			if (Settings::debugStepsToTikz) {
				thp.layout();
				thp.writeTo("cad_debug.tex");
			}
		}
		std::size_t dim() const {
			return mVariables.size();
		}
		const auto& getVariables() const {
			return mVariables;
		}
		const auto& getConstraints() const {
			return mConstraints;
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
		
		ConflictGraph generateConflictGraph() const {
			ConflictGraph cg(mConstraints.size());
			
			//@todo generate graph

			return cg;
		}
	};
}
}
