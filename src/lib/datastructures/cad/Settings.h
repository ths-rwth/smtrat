#pragma once

#include <carl/core/rootfinder/IncrementalRootFinder.h>

namespace smtrat {
namespace cad {
	enum class Incrementality { NONE, SIMPLE, FULL };
	enum class Backtracking { ORDERED, UNORDERED, HIDE };
	enum class ProjectionType { Brown, McCallum, Hong };
	enum class SampleCompareStrategy { Integer, Numeric, Value };
	enum class FullSampleCompareStrategy { Integer, Numeric, Value };
	enum class MISHeuristic { TRIVIAL, GREEDY, GREEDY_PRE, GREEDY_WEIGHTED, HYBRID};
	enum class CoreHeuristic { BySample, PreferProjection, PreferSampling };
	using RootSplittingStrategy = carl::rootfinder::SplittingStrategy;
}
}
