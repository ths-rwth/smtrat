#pragma once

#include "../Common.h"
#include "../helper/CADConstraints.h"
#include "../projection/Projection.h"

#include "Settings.h"

namespace smtrat {
namespace cad {
namespace debug {
	class Projection {
		using Settings = DebugSettings;
	private:
		CADConstraints<Settings::backtracking> mConstraints;
		ProjectionT<Settings> mProjection;
	public:
		Projection(const Variables& vars):
			mConstraints(
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.addPolynomial(mProjection.normalize(p), cid, isBound); },
				[&](const UPoly& p, std::size_t cid, bool isBound){ mProjection.removePolynomial(mProjection.normalize(p), cid, isBound); }
			),
			mProjection(mConstraints)
		{
			mConstraints.reset(vars);
			mProjection.reset();
		}
		
		auto& getProjection() {
			return mProjection;
		}
		
		void add(const ConstraintT& c) {
			mConstraints.add(c);
		}
	};
}
}
}
