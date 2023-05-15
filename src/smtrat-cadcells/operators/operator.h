#pragma once

#include "../datastructures/derivation.h"
#include "../datastructures/representation.h"

/**
 * Projection operators.
 * 
 * Currently, only the McCallum based operator is implemented.
 * 
 * ## Relevant projection functions
 * 
 * We refer to @ref algorithms for usage examples.
 * 
 * ### Cells
 * - project_cell_properties
 * - project_basic_properties
 * - delineate_properties
 * - project_delineated_cell_properties
 * 
 * ### Coverings
 * 
 * - project_cell_properties (on each cell individually)
 * - project_basic_properties (on each cell individually)
 * - delineate_properties (on each cell individually)
 * - project_covering_properties
 * 
 * ### Delineation
 * 
 * - project_basic_properties
 * - delineate_properties
 * - project_delineation_properties
 * 
 */
namespace smtrat::cadcells::operators {

enum op { mccallum, mccallum_filtered, mccallum_filtered_all, mccallum_filtered_bounds, mccallum_filtered_samples, mccallum_filtered_all_selective, mccallum_filtered_all_compound, mccallum_filtered_all_compound_ew };
static const char * OpStrings[] = { "mccallum", "mccallum_filtered", "mccallum_filtered_all", "mccallum_filtered_bounds", "mccallum_filtered_samples", "mccallum_filtered_all_selective", "mccallum_filtered_all_compound", "mccallum_filtered_all_compound_ew" };

inline std::ostream& operator<<(std::ostream& os, op op){
    return os << OpStrings[op];
}

template <op Op>
struct PropertiesSet;

/**
 * Project basic properties, i.e. independent from any sample or delineation.
 */
template <op Op>
inline bool project_basic_properties(datastructures::DelineatedDerivation<typename PropertiesSet<Op>::type>& deriv);

/**
 * Delineate properties.
 */
template <op Op>
inline void delineate_properties(datastructures::DelineatedDerivation<typename PropertiesSet<Op>::type>& deriv);
/**
 * Delineate properties.
 */
template <op Op>
inline void delineate_properties(datastructures::SampledDerivation<typename PropertiesSet<Op>::type>& deriv);

/**
 * Project cell properties that depend on a delineation.
 */
template <op Op>
inline bool project_delineated_cell_properties(datastructures::CellRepresentation<typename PropertiesSet<Op>::type>& deriv, bool cell_represents = true);

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
inline bool project_covering_properties(datastructures::CoveringRepresentation<typename PropertiesSet<Op>::type>& repr);

} 
