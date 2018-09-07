#pragma once

#include "Projection_QE.h"

#include "../../cad/Common.h"
#include "../../cad/lifting/LiftingTree.h"
#include "../../cad/helper/CADConstraints.h"

//#include "Projection_QE.h"

namespace smtrat {
namespace cad {
	template<typename Settings>
	class CAD_QE {
	private:
		Variables mVariables;
		CADConstraints<Settings::backtracking> mConstraints;
		Projection_QE<Settings> mProjection;
		LiftingTree<Settings> mLifting;

    std::size_t idPL(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}

		std::size_t idLP(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return dim() - level + 1;
		}
	public:
		CAD_QE():
			mConstraints(
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(mProjection.normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addEqConstraint(mProjection.normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(mProjection.normalize(p), cid, isBound); }
			),
			mProjection(mConstraints),
			mLifting(mConstraints)
		{
			mProjection.setRemoveCallback([&](std::size_t level, const SampleLiftedWith& mask){
				mLifting.removedPolynomialsFromLevel(idPL(level), mask);
			});
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

    void reset(const Variables& vars) {
      mVariables = vars;
			mConstraints.reset(mVariables);
			mProjection.reset();
			mLifting.reset(Variables(vars.rbegin(), vars.rend()));
    }

		void addConstraint(const ConstraintT& c) {
			mConstraints.add(c);
		}

		void removePolynomial(std::size_t level, std::size_t id) {
			mProjection.removeProjectionFactor(level, id);
		}

    void lift() {
			// Fragen, ob die naechsten beiden Zeilen wirklich gebraucht werden
      mLifting.resetFullSamples();
      mLifting.restoreRemovedSamples();

      while (mLifting.hasNextSample()) {
        auto it = mLifting.getNextSample();
        Sample& s = *it;

        assert(0 <= it.depth() && it.depth() < cad.dim());

        auto polyID = mProjection.getPolyForLifting(idLP(it.depth() + 1), s.liftedWith());

        if (polyID) {
					// Polynom kann eventuell durch simplifyCAD geloescht worden sein
					if(mProjection.hasPolynomialById(idLP(it.depth() + 1), *polyID)) {
						const auto& poly = mProjection.getPolynomialById(idLP(it.depth() + 1), *polyID);
	          mLifting.liftSample(it, poly, *polyID);
					}
        } else {
          mLifting.removeNextSample();
					mLifting.addTrivialSample(it);
        }
      }
    }
	};
}
}
