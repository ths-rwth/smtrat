#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <op Op>
struct properties_set;

template <op Op>
void project_basic_properties(datastructures::base_derivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void delineate_properties(datastructures::delineated_derivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void project_delineated_cell_properties(datastructures::cell_representation<typename properties_set<Op>::type>& deriv, bool cell_represents = true);

template <op Op>
void project_cell_properties(datastructures::sampled_derivation<typename properties_set<Op>::type>& deriv);

template <op Op>
void project_covering_properties(datastructures::covering_representation<typename properties_set<Op>::type>& repr);

} 
