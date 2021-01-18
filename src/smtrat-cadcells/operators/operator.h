#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <typename Op>
class properties_set;

template <typename Op>
void project_basic_properties(datastructures::base_derivation<properties_set<Op>>& deriv);

template <typename Op>
datastructures::delineation delineate_properties(datastructures::base_derivation<properties_set<Op>>& deriv);

template <typename Op>
void project_delineated_cell_properties(datastructures::cell_representation<Op>& deriv);

template <typename Op>
void project_cell_properties(datastructures::base_derivation<properties_set<Op>>& deriv);

template <typename Op>
void project_covering_properties(datastructures::covering_representation<properties_set<Op>>& repr);

} 
