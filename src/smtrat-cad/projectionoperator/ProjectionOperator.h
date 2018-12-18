#pragma once

#include "../common.h"

#include "Brown.h"
#include "Collins.h"
#include "Hong.h"
#include "McCallum.h"
#include "McCallum_partial.h"
#include "utils.h"

namespace smtrat {
namespace cad {

struct ProjectionOperator {
	template<typename Callback>
	void operator()(ProjectionType pt, const UPoly& p, carl::Variable variable, Callback&& cb) const {
		switch (pt) {
		case ProjectionType::Collins:
			return projection::collins::single(p, variable, cb);
		case ProjectionType::Hong:
			return projection::hong::single(p, variable, cb);
		case ProjectionType::McCallum:
			return projection::mccallum::single(p, variable, cb);
		case ProjectionType::McCallum_partial:
			return projection::mccallum_partial::single(p, variable, cb);
		case ProjectionType::Brown:
			return projection::brown::single(p, variable, cb);
		default:
			SMTRAT_LOG_ERROR("smtrat.cad", "Selected a projection operator that is not implemented.");
			return;
		}
	}
	template<typename Callback>
	void operator()(ProjectionType pt, const UPoly& p, const UPoly& q, carl::Variable variable, Callback&& i) const {
		switch (pt) {
		case ProjectionType::Collins:
			return projection::collins::paired(p, q, variable, i);
		case ProjectionType::Hong:
			return projection::hong::paired(p, q, variable, i);
		case ProjectionType::McCallum:
			return projection::mccallum::paired(p, q, variable, i);
		case ProjectionType::McCallum_partial:
			return projection::mccallum_partial::paired(p, q, variable, i);
		case ProjectionType::Brown:
			return projection::brown::paired(p, q, variable, i);
		default:
			SMTRAT_LOG_ERROR("smtrat.cad", "Selected a projection operator that is not implemented.");
			return;
		}
	}
};

} // namespace cad
} // namespace smtrat
