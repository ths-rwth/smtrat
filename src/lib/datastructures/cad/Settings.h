#pragma once

#include <carl/core/rootfinder/IncrementalRootFinder.h>

namespace smtrat {
namespace cad {
	enum class Incrementality: unsigned { NONE, SIMPLE, FULL };
	enum class Backtracking: unsigned { ORDERED, UNORDERED, HIDE };
	enum class ProjectionType: unsigned { Brown, McCallum, Hong };
	using RootSplittingStrategy = carl::rootfinder::SplittingStrategy;
}
}
