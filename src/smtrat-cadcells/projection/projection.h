#pragma once

namespace smtrat::cadcells::projection {

enum class projection_type {
    McCallum
};


template<projection_type type>
/**
 * @brief 
 * @param properties_in of level i
 * @param order
 * @param sample 
 * @param properties_out of level i-1
 * @return 
 */
cell_at_level project(const properties& properties_in, const var_order& order, const Model& sample, properties& properties_out);

// TODO how to extend to covering?

} // namespace smtrat::cadcells::projection
