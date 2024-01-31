#include "FourierMotzkinQE.h"
#include "../util/EqualitySubstitution.h"
#include "eigen_helpers.h"


namespace smtrat::qe::fm {

FormulaT FourierMotzkinQE::eliminateQuantifiers() {
    // gather quantified variables
    std::vector<carl::Variable> elimination_vars;
    for (const auto& [type, vars] : m_query) {
        assert(type == QuantifierType::EXISTS); // Only support existential for now
        elimination_vars.insert(elimination_vars.end(), vars.begin(), vars.end());
    }
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().vars(elimination_vars.size()));

    // gather input constraints
    FormulasT constraints;
    if (m_formula.type() == carl::FormulaType::CONSTRAINT) constraints.push_back(m_formula);
    else constraints = m_formula.subformulas();
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().input(constraints.size()));

    for (const auto& c : constraints) {
        assert(c.type() == carl::FormulaType::CONSTRAINT);
        assert(
            c.constraint().relation() == carl::Relation::LEQ ||
            c.constraint().relation() == carl::Relation::EQ // TODO: what about strict constraints?
        );
    }


    // eliminate variables using equalities
    qe::util::EquationSubstitution es(constraints, elimination_vars);
    if (!es.apply()) {
        SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().elim_eq(elimination_vars.size()));
        SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().eq_conflict());
        return FormulaT(carl::FormulaType::FALSE);
    }
    constraints      = es.remaining_constraints();
    elimination_vars = es.remaining_variables();
    SMTRAT_LOG_DEBUG("smtrat.qe","Constraints after es: " << constraints);
    SMTRAT_STATISTICS_CALL(FMQEStatistics::get_instance().elim_eq(elimination_vars.size()));

    if (elimination_vars.empty()) {
        return FormulaT(carl::FormulaType::AND, constraints);
    }
    
    // filter finished constraints from remaining constraints
    FormulasT filtered;
    for (const auto& c : constraints) {
        auto vars = carl::variables(c).as_set();
        if (std::any_of(elimination_vars.begin(),
                        elimination_vars.end(),
                        [&vars](const auto v){ return vars.contains(v); })
        ) { 
            filtered.push_back(c);
        } else m_finished.insert(c);
    }
    constraints = filtered;
    SMTRAT_LOG_DEBUG("smtrat.qe","Constraints after filtering: " << constraints);

    // map from variables to indices
    m_var_idx = qe::util::VariableIndex(elimination_vars);
    m_var_idx.gather_variables(constraints);
    
    // gather elimination indices
    std::vector<std::size_t> elim_cols;
    for (std::size_t i = 0; i < elimination_vars.size(); ++i) {
        elim_cols.push_back(i);
    }

    // transform to matrix-vector representation
    matrix_t m = matrix_t::Zero(constraints.size(), m_var_idx.size());
    vector_t b = vector_t::Zero(constraints.size());

    for (std::size_t i = 0; i < constraints.size(); ++i) {
        for (const auto& t : constraints[i].constraint().lhs()) {
            if (t.is_constant()) b(i) = Rational(-1)*t.coeff();
            else {
                assert(t.is_single_variable());
                m(i, m_var_idx.index(t.single_variable())) = t.coeff();
            }
        }
    }

    auto [result_m, result_b] = eliminateCols(m, b, elim_cols);
    // convert back
    for (std::size_t i = 0, n_rows = result_m.rows(), n_cols = result_m.cols(); i < n_rows; ++i) {
        Poly lhs = Poly(Rational(-1)*result_b(i));
        for (std::size_t j = 0; j < n_cols; ++j) {
            Rational& coeff = result_m(i,j);
            if (!carl::is_zero(coeff)) {
                lhs += coeff*Poly(m_var_idx.var(j));
            }
        }
        m_finished.insert(FormulaT(lhs, carl::Relation::LEQ));
    }

    return FormulaT(carl::FormulaType::AND, m_finished);
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
        std::cout << "starting iteration\n";
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
        std::cout << "end iteration\n";

    }
    return std::make_pair(resultConstraints, resultConstants);
}



} // namespace smtrat::qe::fm
