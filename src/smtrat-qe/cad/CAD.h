#pragma once

#include "Projection.h"

#include <lib/datastructures/cad/Common.h>
#include <lib/datastructures/cad/lifting/LiftingTree.h>
#include <lib/datastructures/cad/helper/CADConstraints.h>

namespace smtrat::qe::cad {

	template<typename Settings>
	class CAD {
	public:
		using TreeIterator = typename smtrat::cad::LiftingTree<Settings>::Iterator;
	private:
		std::vector<carl::Variable> mVariables;
		smtrat::cad::CADConstraints<Settings::backtracking> mConstraints;
		std::vector<Poly> polynomials;
		Projection<Settings> mProjection;
		smtrat::cad::LiftingTree<Settings> mLifting;

    std::size_t idPL(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
		std::size_t idLP(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
	public:
		CAD():
			mConstraints(
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(smtrat::cad::projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(smtrat::cad::projection::normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(smtrat::cad::projection::normalize(p), cid, isBound); }
			),
			mProjection(mConstraints),
			mLifting(mConstraints)
		{
			mProjection.setRemoveCallback([&](std::size_t level, const smtrat::cad::SampleLiftedWith& mask){
				mLifting.removedPolynomialsFromLevel(idPL(level), mask);
			});
		}

		void reset(const std::vector<carl::Variable>& vars) {
			mVariables = vars;
			mConstraints.reset(mVariables);
			mProjection.reset();
			mLifting.reset(std::vector<carl::Variable>(vars.rbegin(), vars.rend()));
		}

		std::size_t dim() const {
			return mVariables.size();
		}
		const auto& getProjection() const {
			return mProjection;
		}
		const auto& getLifting() const {
			return mLifting;
		}

		void addConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Adding " << c);
			mConstraints.add(c);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
		}
		void removeConstraint(const ConstraintT& c) {
			SMTRAT_LOG_DEBUG("smtrat.cad", "Removing " << c);
			auto mask = mConstraints.remove(c);
			mLifting.removedConstraint(mask);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current projection:" << std::endl << mProjection);
			SMTRAT_LOG_DEBUG("smtrat.cad", "Current sampletree:" << std::endl << mLifting.getTree());
    }

		void addPolynomial(const Poly& p) {
		  polynomials.push_back(p);
		}
		void removePolynomial(std::size_t level, std::size_t id) {
			mProjection.removeProjectionFactor(level, id);
		}

		void project() {
			for(auto it = polynomials.begin(); it != polynomials.end(); it++) {
				mConstraints.add(ConstraintT(*it, carl::Relation::EQ));
			}
			polynomials.clear();
		}
    void lift() {
      mLifting.resetFullSamples();
      mLifting.restoreRemovedSamples();

      while (mLifting.hasNextSample()) {
        auto it = mLifting.getNextSample();
        auto& s = *it;
				SMTRAT_LOG_DEBUG("smtrat.cad", "Sample " << s << " at depth " << it.depth());
        SMTRAT_LOG_DEBUG("smtrat.cad", "Current sample: " << mLifting.printSample(it));
        assert(0 <= it.depth() && it.depth() < dim());
        auto polyID = mProjection.getPolyForLifting(idLP(it.depth() + 1), s.liftedWith());
        if(polyID) {
					if(mProjection.hasPolynomialById(idLP(it.depth() + 1), *polyID)) {
						const auto& poly = mProjection.getPolynomialById(idLP(it.depth() + 1), *polyID);
						SMTRAT_LOG_DEBUG("smtrat.cad", "Lifting " << s << " with " << poly);
	          mLifting.liftSample(it, poly, *polyID);
					}
        }else {
          mLifting.removeNextSample();
					mLifting.addTrivialSample(it);
        }
      }

			std::size_t number_of_cells = 0;
		  const auto& tree = mLifting.getTree();
		  for(auto it = tree.begin_leaf(); it != tree.end_leaf(); ++it) {
			  ++number_of_cells;
		  }
      SMTRAT_LOG_WARN("smtrat.cad", "Got " << number_of_cells << " cells");
    }
	};

}
