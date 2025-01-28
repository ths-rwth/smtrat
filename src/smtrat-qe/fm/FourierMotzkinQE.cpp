#include "FourierMotzkinQE.h"
#include "../util/EqualitySubstitution.h"
#include "eigen_helpers.h"


namespace smtrat::qe::fm {

FormulaT FourierMotzkinQE::eliminateQuantifiers() {

    // gather quantified variables
    std::vector<carl::Variable> elim_vars = gather_elimination_variables();
    SMTRAT_LOG_DEBUG("smtrat.qe.fm","elim vars:" << elim_vars);
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().vars(elim_vars.size()));

    // gather input constraints
    FormulasT constraints;
    if (m_formula.type() == carl::FormulaType::CONSTRAINT) constraints.push_back(m_formula);
    else constraints = m_formula.subformulas();
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().input(constraints.size()));

    for (const auto& c : constraints) {
        assert(c.type() == carl::FormulaType::CONSTRAINT);
        assert(
            c.constraint().relation() == carl::Relation::LEQ ||
            c.constraint().relation() == carl::Relation::LESS ||
            c.constraint().relation() == carl::Relation::EQ
        );
    }

    // eliminate variables using equalities
    qe::util::EquationSubstitution es(constraints, elim_vars);
    if (!es.apply()) {
        SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().elim_eq(elim_vars.size()));
        SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().eq_conflict());
        return FormulaT(carl::FormulaType::FALSE);
    }
    constraints = es.remaining_constraints();
    elim_vars   = es.remaining_variables();
    SMTRAT_LOG_DEBUG("smtrat.qe","Constraints after es: " << constraints);
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().elim_eq(elim_vars.size()));

    if (elim_vars.empty()) {
        return (constraints.size() == 1) ? constraints.front() 
                                         : FormulaT(carl::FormulaType::AND, constraints);;
    }

    // map from variables to indices
    m_var_idx = qe::util::VariableIndex(elim_vars);
    m_var_idx.gather_variables(constraints);
    m_first_parameter_col = elim_vars.size();
    SMTRAT_LOG_DEBUG("smtrat.qe","after gather variables");

    std::vector<Matrix::ColIndex> elim_var_indices;
    for (ColIndex j = 0; j < m_first_parameter_col; ++j) elim_var_indices.push_back(j);
    m_matrix = build_initial_matrix(constraints);

    while(!elim_var_indices.empty()) {
        // choose next variable to be eliminated
        std::size_t min_new_cs = m_matrix.n_rows()*(m_matrix.n_rows() + 1) + 1;
        ColIndex chosen_col = 0;
        for (const ColIndex j : elim_var_indices) {
            std::size_t n_lbs = 0, n_ubs = 0;
            auto col_end = m_matrix.col_end(j);
            for (auto col_it = m_matrix.col_begin(j); col_it != col_end; ++col_it) {
                if (col_it->value < 0) ++n_lbs;
                else ++n_ubs;
            }
            
            std::size_t min_j = n_lbs*n_ubs + (m_matrix.n_rows() - n_lbs - n_ubs);
            if (min_j < min_new_cs) {
                min_new_cs = min_j;
                chosen_col = j;
                if (min_j == 0) break;
            }
        }

        // collect lbs and ubs
        Matrix m(min_new_cs, m_matrix.n_cols());
        std::vector<RowIndex> lbs, ubs;
        auto col_it  = m_matrix.col_begin(chosen_col);
        auto col_end = m_matrix.col_end(chosen_col);
        RowIndex nb = 0;
        for (; col_it != col_end; ++col_it) {
            for(; nb < col_it.row(); ++nb) {
                m.append_row(m_matrix.row_begin(nb), m_matrix.row_end(nb));
            }
            ++nb;
            if (col_it->value < 0) lbs.push_back(col_it.row());
            else if (col_it->value > 0) ubs.push_back(col_it.row());
        }
        for(; nb < m_matrix.n_rows(); ++nb) {
            m.append_row(m_matrix.row_begin(nb), m_matrix.row_end(nb));
        }

        SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().node(lbs.size() * ubs.size()));
        // generate new constraints
        for (const RowIndex l : lbs) {
            Rational coeff_l = (-1)*m_matrix.coeff(l, chosen_col);
            for (const RowIndex u : ubs) {
                Rational coeff_u = m_matrix.coeff(u, chosen_col);
                auto combined_row = m_matrix.combine(l, coeff_u, u, coeff_l);
                if (combined_row.empty()) continue;
                qe::util::gcd_normalize(combined_row);
                if (combined_row.front().col_index < m_first_parameter_col) {
                    // row still contains quantified variables
                    m.append_row(combined_row.begin(), combined_row.end());
                } else if (is_trivial(combined_row)) {
                    if (is_conflict(combined_row)) return FormulaT(carl::FormulaType::FALSE);
                } else {
                    collect_constraint(combined_row);
                }
            }
        }

        elim_var_indices.erase(std::find(elim_var_indices.begin(), elim_var_indices.end(), chosen_col));

        Matrix irred_m(m.n_rows(), m.n_cols());
        auto irred_rows = util::simple_irredundant_rows(m_matrix, constant_column());
        for (const auto r : irred_rows) irred_m.append_row(m.row_begin(r), m.row_end(r));

        m_matrix = irred_m;
    }

    std::vector<FormulaT> conjuncts;
    conjuncts.reserve(m_found_rows.size());
    for (const auto& r : m_found_rows) conjuncts.push_back(constraint_from_row(r));

    return FormulaT(carl::FormulaType::AND, conjuncts);
}


std::pair<matrix_t, vector_t> FourierMotzkinQE::eliminateCol(const matrix_t& constraints,
                                                             const vector_t& constants,
                                                             std::size_t col,
                                                             bool conservative) {
    std::vector<std::size_t> nbs, ubs, lbs;

    // initialize: detect upper and lower bounds
    for (Eigen::Index row = 0; row < constraints.rows(); ++row) {
        if (carl::is_zero(constraints(row, col))) nbs.push_back(row);
        else if (carl::is_positive(constraints(row, col))) ubs.push_back(row);
        else lbs.push_back(row);
    }

    // initialize result
    Eigen::Index n_new_constr = nbs.size() + (ubs.size() * lbs.size());
    matrix_t newConstraints = matrix_t(n_new_constr, constraints.cols());
    vector_t newConstants = vector_t(n_new_constr);

    // compute new constraints
    std::vector<Eigen::Index> emptyRows;
    Eigen::Index row = 0;
    for (; row < nbs.size(); ++row) {
        newConstraints.row(row) = constraints.row(nbs[row]);
        newConstants.row(row) = constants.row(nbs[row]);
    }

    for (; row < n_new_constr; ++row) {
        std::size_t combinationIndex = row - nbs.size();
        std::size_t lb_idx = combinationIndex / ubs.size();
        std::size_t ub_idx = combinationIndex % ubs.size();
        assert(lb_idx < lbs.size());
        assert(ub_idx < ubs.size());
        newConstraints.row(row) = (constraints(ubs[ub_idx], col) * constraints.row(lbs[lb_idx]))
                                - (constraints(lbs[lb_idx], col) * constraints.row(ubs[ub_idx]));
        newConstants(row) = (constraints(ubs[ub_idx], col) * constants(lbs[lb_idx]))
                            - (constraints(lbs[lb_idx], col) * constants(ubs[ub_idx]));
        
        if (newConstraints.row(row).isZero()) emptyRows.push_back(row);
    }

    assert(vector_t(newConstraints.col(col)) == vector_t::Zero(newConstants.rows()));

    // cleanup if demanded
    if (!conservative) { newConstraints = removeCol(newConstraints, col); }

    // Optimizer<Number> opt(newConstraints, newConstants); TODO
    // auto red = opt.redundantConstraints();
    // newConstraints = removeRows(newConstraints, red);
    // newConstants = removeRows(newConstants, red);
    return std::make_pair(newConstraints, newConstants);
}

std::pair<matrix_t, vector_t> FourierMotzkinQE::eliminateCols(const matrix_t &constraints,
                                                              const vector_t constants,
                                                              const std::vector<std::size_t> &cols,
                                                              bool conservative) {
    auto resultConstraints = constraints;
    auto resultConstants = constants;
    auto dimensionsToEliminate = cols;
    while (!dimensionsToEliminate.empty()) {
        std::tie(resultConstraints, resultConstants) = 
                                    eliminateCol(resultConstraints, resultConstants,
                                                dimensionsToEliminate.front(), conservative);
        // update the indices if the matrix and vector have changed dimensions
        if (!conservative) {
            // decrement this index, as one dimension before has been eliminated.
            for (auto &idx: dimensionsToEliminate) {
                if (idx > dimensionsToEliminate.front()) --idx;
            }
        }
        dimensionsToEliminate.erase(std::begin(dimensionsToEliminate));
    }
    return std::make_pair(resultConstraints, resultConstants);
}



} // namespace smtrat::qe::fm
