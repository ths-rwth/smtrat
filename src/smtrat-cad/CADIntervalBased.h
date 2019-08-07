#pragma once

#include <vector>

#include "common.h"
#include "projection/Projection.h"
#include "lifting/LiftingLevel.h"
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
		std::vector<LiftingLevel<Settings>> mLifting;
		ProjectionT<Settings> mProjection;
		
		// ID scheme for variables x,y,z:
		// Projection: x=1,y=2,z=3
		// Lifting: x=3,y=2,z=1,anonymous=0
		std::size_t idPL(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
		std::size_t idLP(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}

	public:
		debug::TikzHistoryPrinter thp;
		CADIntervalBased():
			mConstraints(
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(projection::normalize(p), cid, isBound); }
			),
			mProjection(mConstraints),
			mLifting()
		{
			//@todo what to initialize
			mLifting.append(LiftingLevel(mConstraints));
			
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
		const auto& getProjection() const {
			return mProjection;
		}
		const auto& getLifting() const {
			return mLifting;
		}
		//const auto& getConstraints() const {
		//	return mConstraints.indexed();
		//}
		//const auto& getConstraintMap() const {
		//	return mConstraints.ordered();
		//}
		//bool isIdValid(std::size_t id) const {
		//	return mConstraints.valid(id);
		//}
		//const auto& getBounds() const {
		//	return mConstraints.bounds();
		//}
		void reset(const std::vector<carl::Variable>& vars) {
			mVariables = vars;
			mConstraints.clear();
			mProjection.reset();
			mLifting.reset(std::vector<carl::Variable>(vars.rbegin(), vars.rend()));
		}

		//@todo add constraint to lifting level
		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			//mConstraints.add(c);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current intervals in lifting level:" << std::endl << mLifting.getUnsatIntervals());
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			//auto mask = mConstraints.remove(c);
			//mLifting.removedConstraint(mask);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current intervals in lifting level:" << std::endl << mLifting.getUnsatIntervals());
		}
		
		Answer check(Assignment& assignment, std::vector<FormulaSetT>& mis) {
			LiftingLevel currentLevel = mLifting.back();
			// check for (-inf, +inf) in the unsat intervals
			if(currentLevel.isSingletonCover()) {
				return Answer::UNSAT;
			}

			CADCoreIntervalBased<Settings::coreIntervalBasedHeuristic> cad;
			auto res = cad(assignment, *this);
			
			/*Assignment newsample = std::map<mLifting.getCurrentSample.get>;
			assignment.insert(); */

			//@todo check

			return Answer::UNKNOWN;
		}
		
		ConflictGraph generateConflictGraph() const {
			ConflictGraph cg(mConstraints.size());
			
			//@todo generate graph

			return cg;
		}
	};
}
}
