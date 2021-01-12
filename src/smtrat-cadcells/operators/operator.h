#pragma once

namespace smtrat::cadcells::operators {

enum op { mccallum };

template <typename T>
class derivation;

template <typename T>
void project_basic_properties(derivation& deriv);

template <typename T>
delineation delineate_properties(derivation& deriv);

template <typename T>
void project_delineated_cell_properties(derivation& deriv, const cell_representation& repr);

template <typename T>
void project_cell_properties(derivation& deriv);

} 
