#pragma once

#include <carl/core/rootfinder/IncrementalRootFinder.h>

namespace smtrat {
namespace cad {
	enum class Incrementality { NONE, SIMPLE, FULL };
	enum class Backtracking { ORDERED, UNORDERED, HIDE };
	enum class ProjectionType { Brown, McCallum, Hong };
	enum class SampleCompareStrategy { Integer, Value };
	enum class FullSampleCompareStrategy { Integer, Value };
	enum class MISHeuristic { TRIVIAL, GREEDY };
	using RootSplittingStrategy = carl::rootfinder::SplittingStrategy;
}
}
