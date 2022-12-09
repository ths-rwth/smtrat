#pragma once
#include "../Tableau.h"

namespace smtrat::fmplex {

class Gauss {
    public:
    virtual void init(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) = 0;
    virtual void apply_gaussian_elimination() = 0;
    virtual FMPlexTableau get_transformed_inequalities() = 0;
    virtual std::optional<Conflict> find_conflict() = 0;
    virtual void assign_variables(std::map<std::size_t, DeltaRational>&) = 0;
};

} // namespace smtrat::fmplex

#include "FMPlexGauss.h"
//#include "EigenGauss.h"