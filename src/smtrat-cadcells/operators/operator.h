#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <op Op>
struct properties_set;

template <op Op>
void project_basic_properties(datastructures::BaseDerivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void delineate_properties(datastructures::DelineatedDerivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void project_delineated_cell_properties(datastructures::CellRepresentation<typename properties_set<Op>::type>& deriv, bool cell_represents = true);

template <op Op>
bool project_cell_properties(datastructures::SampledDerivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void project_covering_properties(datastructures::CoveringRepresentation<typename properties_set<Op>::type>& repr);

} 
