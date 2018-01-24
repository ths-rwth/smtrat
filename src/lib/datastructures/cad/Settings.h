#pragma once

#include <carl/core/rootfinder/IncrementalRootFinder.h>

namespace smtrat {
namespace cad {
	enum class Incrementality { NONE, SIMPLE, FULL };
	enum class Backtracking { ORDERED, UNORDERED, HIDE };
	enum class ProjectionType { Brown, McCallum, Hong };
	enum class SampleCompareStrategy { Integer, Numeric, Value };
	enum class FullSampleCompareStrategy { Integer, Numeric, Value };
	using SampleHeuristic = carl::RANSampleHeuristic;
	enum class MISHeuristic { TRIVIAL, GREEDY, GREEDY_PRE, GREEDY_WEIGHTED, HYBRID};
	enum class CoreHeuristic { BySample, PreferProjection, PreferSampling };
	using RootSplittingStrategy = carl::rootfinder::SplittingStrategy;

	struct BaseSettings {
		static constexpr Incrementality incrementality = Incrementality::NONE;
		static constexpr Backtracking backtracking = Backtracking::ORDERED;
		
		static constexpr ProjectionType projectionOperator = cad::ProjectionType::Brown;
		static constexpr CoreHeuristic coreHeuristic = cad::CoreHeuristic::PreferProjection;
		
		static constexpr MISHeuristic misHeuristic = cad::MISHeuristic::GREEDY;
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		
		static constexpr SampleHeuristic sampleHeuristic = cad::SampleHeuristic::Default;
		static constexpr SampleCompareStrategy sampleComparator = cad::SampleCompareStrategy::Integer;
		static constexpr FullSampleCompareStrategy fullSampleComparator = cad::FullSampleCompareStrategy::Integer;
		static constexpr RootSplittingStrategy rootSplittingStrategy = cad::RootSplittingStrategy::DEFAULT;
	};
}
}
