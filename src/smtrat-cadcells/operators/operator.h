#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

/**
 * Projection operators.
 * 
 * Currently, only the McCallum based operator is implemented.
 * 
 */
namespace smtrat::cadcells::operators {

enum op { mccallum };

template <op Op>
struct PropertiesSet;

/**
 * Project basic properties, i.e. independent from any sample or delineation.
 */
template <op Op>
void project_basic_properties(datastructures::DelineatedDerivation<typename PropertiesSet<Op>::type>& deriv);

/**
 * Delineate properties.
 */
template <op Op>
inline void delineate_properties(datastructures::DelineatedDerivation<typename PropertiesSet<Op>::type>& deriv);

/**
 * Project cell properties that depend on a delineation.
 */
template <op Op>
inline void project_delineated_cell_properties(datastructures::CellRepresentation<typename PropertiesSet<Op>::type>& deriv, bool cell_represents = true);

/**
 * Project cell properties.
 * 
 * Returns false iff the given operator is incomplete and cannot cover the given case (i.e. on nullification with McCallum).
 */
template <op Op>
inline bool project_cell_properties(datastructures::SampledDerivation<typename PropertiesSet<Op>::type>& deriv);

/**
 * Project covering properties.
 */
template <op Op>
inline void project_covering_properties(datastructures::CoveringRepresentation<typename PropertiesSet<Op>::type>& repr);

/**
 * Project delineation properties.
 */
template <op Op>
void project_delineation_properties(datastructures::DelineationRepresentation<typename PropertiesSet<Op>::type>& repr);

} 
