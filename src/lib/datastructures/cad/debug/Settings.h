#pragma once

#include "../Common.h"
#include "../Settings.h"

namespace smtrat {
namespace cad {
namespace debug {
	
	struct DebugSettings {
		static constexpr Incrementality incrementality = Incrementality::NONE;
		static constexpr Backtracking backtracking = Backtracking::ORDERED;
		
		static constexpr ProjectionType projectionOperator = cad::ProjectionType::Brown;
		static constexpr CoreHeuristic coreHeuristic = cad::CoreHeuristic::PreferProjection;
		
		static constexpr MISHeuristic misHeuristic = cad::MISHeuristic::GREEDY;
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		
		static constexpr SampleCompareStrategy sampleComparator = cad::SampleCompareStrategy::Default;
		static constexpr FullSampleCompareStrategy fullSampleComparator = cad::FullSampleCompareStrategy::Default;
		static constexpr RootSplittingStrategy rootSplittingStrategy = cad::RootSplittingStrategy::DEFAULT;
	};
	
}
}
}
