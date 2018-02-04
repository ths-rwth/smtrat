#pragma once

#include <algorithm>
#include <list>
#include <utility>
#include <vector>

#include "../Common.h"

#include "BaseProjection.h"

namespace smtrat {
namespace cad {
	
	template<Incrementality incrementality, Backtracking backtracking, typename Settings>
	class Projection: public BaseProjection<Settings> {};
	
	template<typename Settings>
	using ProjectionT = Projection<Settings::incrementality, Settings::backtracking, Settings>;
}
}

#include "Projection_NO.h"
#include "Projection_NU.h"
#include "Projection_S.h"
#include "Projection_F.h"
#include "Projection_EC.h"
