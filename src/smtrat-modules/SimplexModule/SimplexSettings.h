/**
 * @file SimplexSettings.h
 * @author Valentin Promies
 *
 * @version 2023-04-28
 * Created on 2023-04-28.
 */

#pragma once

namespace smtrat::simplex {

enum class NEQHandling {
    SPLITTING_ON_DEMAND,
    UPDATE_PERTURBATION,
    PIVOT,
    NONE
};

enum class PivotStrategy {
    BLAND,
    MIN_ROW_MIN_COL,
    FMPLEX
};

}

namespace smtrat {

struct SimplexSettings1 {
    static constexpr auto                   moduleName = "SimplexModule<SimplexSettings1>";
    static constexpr std::size_t  pivots_before_blands = 50;

    static const simplex::NEQHandling     neq_handling = simplex::NEQHandling::SPLITTING_ON_DEMAND;
    static const simplex::PivotStrategy pivot_strategy = simplex::PivotStrategy::MIN_ROW_MIN_COL;
    static constexpr bool    simple_theory_propagation = true;
    static constexpr bool                derive_bounds = true;
    static constexpr bool    reactivate_derived_bounds = derive_bounds && true;
    static constexpr bool   lemmas_from_derived_bounds = derive_bounds && false;
    static constexpr bool     initial_bound_derivation = derive_bounds && true;
    static constexpr bool          derive_bounds_eager = derive_bounds && true;

    static constexpr bool internal_neq_handling() {
        return (neq_handling == simplex::NEQHandling::UPDATE_PERTURBATION) ||
               (neq_handling == simplex::NEQHandling::PIVOT);
    }
};

}
