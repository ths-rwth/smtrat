#pragma once

#include <carl/core/rootfinder/IncrementalRootFinder.h>

namespace smtrat {
namespace cad {
	enum class Incrementality { NONE, SIMPLE, FULL };
	enum class Backtracking { ORDERED, UNORDERED, HIDE };
	enum class ProjectionType { Brown, McCallum, Hong };
	enum class SampleCompareStrategy { Value, Integer };
	enum class FullSampleCompareStrategy { RootIntValue };
	using RootSplittingStrategy = carl::rootfinder::SplittingStrategy;
}
}
