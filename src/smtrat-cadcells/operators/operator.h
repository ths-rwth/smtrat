#pragma once

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <typename T>
class properties;

template <typename T>
void project_basic_properties(datastructures::projections& projections, properties<T>& properties, const assignment& sample);

template <typename T>
delineation delineate_properties(datastructures::projections& projections, properties<T>& properties, const assignment& sample);

template <typename T>
void project_cell_properties(datastructures::projections& projections, properties<T>& properties, const assignment& sample, const delineation& del, const cell_representation& repr);

} 
