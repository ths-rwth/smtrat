#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <op Op>
struct PropertiesSet;

template <op Op>
inline void project_basic_properties(datastructures::BaseDerivation<typename PropertiesSet<Op>::type>& deriv);

template <op Op>
inline void delineate_properties(datastructures::DelineatedDerivation<typename PropertiesSet<Op>::type>& deriv);

template <op Op>
inline void project_delineated_cell_properties(datastructures::CellRepresentation<typename PropertiesSet<Op>::type>& deriv, bool cell_represents = true);

template <op Op>
inline bool project_cell_properties(datastructures::SampledDerivation<typename PropertiesSet<Op>::type>& deriv);

template <op Op>
inline void project_covering_properties(datastructures::CoveringRepresentation<typename PropertiesSet<Op>::type>& repr);

} 
