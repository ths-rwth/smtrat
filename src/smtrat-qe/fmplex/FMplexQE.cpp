#include <iostream>
#include <fstream>

#include "FMplexQE.h"

namespace smtrat::qe::fmplex {

FormulaT FMplexQE::eliminate_quantifiers() {
    SMTRAT_LOG_DEBUG("smtrat.qe","input: " << m_query << ", " << m_formula);

    m_nodes.push_back(build_initial_system());

    while (!m_nodes.empty()) {
        Node& n = m_nodes.back();
        SMTRAT_LOG_DEBUG("smtrat.qe","Next node:" << n);

        switch (n.type) {
        case Node::Type::CONFLICT:
            return FormulaT(carl::FormulaType::FALSE);
        case Node::Type::NBS:
            m_nodes.back() = unbounded_elimination(n);
            break;
        case Node::Type::LBS:[[fallthrough]];
        case Node::Type::UBS:
            if (n.is_finished()) m_nodes.pop_back();
            else m_nodes.push_back(bounded_elimination(n));
            break;
        case Node::Type::FM:
            if (!fm_elimination(n)) return FormulaT(carl::FormulaType::FALSE);
            m_nodes.pop_back();
            break;
        case Node::Type::LEAF:
            m_nodes.pop_back();
            break;
        }
    }

    SMTRAT_LOG_DEBUG("smtrat.qe","after loop");
    if (m_found_rows.empty() && m_found_conjuncts.empty()) return FormulaT(carl::FormulaType::TRUE);
    FormulasT conjuncts;
    conjuncts.reserve(m_found_rows.size() + m_found_conjuncts.size());
    for (const auto& r : m_found_rows) conjuncts.push_back(constraint_from_row(r));
    for (const auto& c : m_found_conjuncts) conjuncts.push_back(c); // TODO: deduplication between the two sets?
    return FormulaT(carl::FormulaType::AND, conjuncts);
}


std::vector<carl::Variable> FMplexQE::gather_elimination_variables() const {
    std::vector<carl::Variable> elimination_vars;
    for (const auto& [type, vars] : m_query) {
        assert(type == QuantifierType::EXISTS); // Only support existential for now
        elimination_vars.insert(elimination_vars.end(), vars.begin(), vars.end());
    }
    return elimination_vars;
}


FormulaT FMplexQE::constraint_from_row(const Row& row) const {
    Poly lhs;
    auto it = row.begin();
    for (; it->col_index < constant_column(); ++it) {
        lhs += it->value*Poly(m_var_idx.var(it->col_index));
    }
    if (it->col_index == constant_column()) {
        lhs += it->value;
        ++it;
    }
    // This method is only applied to pos.lin. combinations, so the delta coeff will be >=0
    if (it->col_index == delta_column()) return FormulaT(lhs, carl::Relation::LESS);
    return FormulaT(lhs, carl::Relation::LEQ);
}


FMplexQE::Matrix FMplexQE::build_initial_matrix(const FormulasT& constraints) {
    // reserve enough space for the matrix
    Matrix m(constraints.size(), m_var_idx.size() + constraints.size() + 2); // +2 : delta & rhs.
    std::size_t non_zeros = 2*constraints.size(); // one origin & at most one delta for each row
    for (const auto& f : constraints) non_zeros += f.constraint().lhs().nr_terms();
    m.reserve(non_zeros);

    // transform each constraint into a row
    for (RowIndex r = 0; r < constraints.size(); ++r) {
        carl::Relation rel = constraints[r].constraint().relation();

        // smtrat automatically converts constraints to < or <=
        assert(rel != carl::Relation::GREATER && rel != carl::Relation::GEQ);
        assert(rel != carl::Relation::NEQ); // we don't support NEQ yet

        Poly lhs = constraints[r].constraint().lhs();
        Rational constant_part = lhs.constant_part();
        lhs -= constant_part;

        Row entries; // TODO: make it so that the contents of the row are actually already in the matrix data
        for (const auto& term : lhs) {
            entries.emplace_back(m_var_idx.index(term.single_variable()), term.coeff());
        }
        // the order in the polynomial may be different from the order in the var index
        std::sort(entries.begin(), entries.end(),
            [](const auto& lhs, const auto& rhs){ return lhs.col_index < rhs.col_index; }
        );

        // constant part, delta, and origin
        if (!carl::is_zero(constant_part)) entries.emplace_back(constant_column(), constant_part);
        if (rel == carl::Relation::LESS)   entries.emplace_back(delta_column(), Rational(1));
        entries.emplace_back(origin_column(r), Rational(1));

        m.append_row(entries.begin(), entries.end());
    }
    return m;
}


Node FMplexQE::build_initial_system() {
    // gather quantified variables
    std::vector<carl::Variable> elim_vars = gather_elimination_variables();
    SMTRAT_LOG_DEBUG("smtrat.qe","elim vars:" << elim_vars);
    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().vars(elim_vars.size()));

    // gather input constraints
    FormulasT constraints;
    if (m_formula.type() == carl::FormulaType::CONSTRAINT) constraints.push_back(m_formula);
    else constraints = m_formula.subformulas();
    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().input(constraints.size()));

    // eliminate variables using equalities
    qe::util::EquationSubstitution es(constraints, elim_vars);
    if (!es.apply()) {
        SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().elim_eq(elim_vars.size()));
        SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().eq_conflict());
        return Node::conflict();
    }
    constraints = es.remaining_constraints();
    elim_vars   = es.remaining_variables();
    SMTRAT_LOG_DEBUG("smtrat.qe","Constraints after es: " << constraints);
    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().elim_eq(elim_vars.size()));
    
    // filter finished constraints from remaining constraints
    FormulasT filtered;
    for (const auto& c : constraints) {
        auto vars = carl::variables(c).as_set();
        if (std::any_of(elim_vars.begin(),
                        elim_vars.end(),
                        [&vars](const auto v){ return vars.contains(v); })
        ) { 
            filtered.push_back(c);
        } else m_found_conjuncts.insert(c);
    }
    constraints = filtered;
    SMTRAT_LOG_DEBUG("smtrat.qe","Constraints after filtering: " << constraints);

    if (elim_vars.empty()) return Node::leaf();

    // map from variables to indices
    m_var_idx = qe::util::VariableIndex(elim_vars);
    m_var_idx.gather_variables(constraints);
    m_first_parameter_col = elim_vars.size();
    SMTRAT_LOG_DEBUG("smtrat.qe","after gather variables");

    // list of columns to eliminate. Initially, this are the first k columns for k = #elim vars
    std::vector<Matrix::ColIndex> elim_var_indices;
    for (ColIndex i = 0; i < m_first_parameter_col; ++i) elim_var_indices.push_back(i);

    SMTRAT_LOG_DEBUG("smtrat.qe","before return");
    return Node(build_initial_matrix(constraints), elim_var_indices);
}


Node FMplexQE::unbounded_elimination(Node& parent) {
    auto new_cols = parent.cols_to_elim;
    new_cols.erase(std::find(new_cols.begin(), new_cols.end(), parent.chosen_col));

    std::size_t n_deleted_rows = parent.eliminators.size();
    Matrix new_matr(parent.matrix.n_rows() - n_deleted_rows, parent.matrix.n_cols());
    new_matr.reserve(parent.matrix.non_zeros_total() - 3*n_deleted_rows); // rough estimate.

    auto col_it  = parent.eliminators.begin();
    auto col_end = parent.eliminators.end();

    std::set<RowIndex> ignore;
    auto ignore_it = parent.ignored.begin();

    for (RowIndex r = 0; r < parent.matrix.n_rows(); ++r) {
        if (col_it != col_end && r == *col_it) ++col_it;
        else {
            new_matr.append_row(parent.matrix.row_begin(r), parent.matrix.row_end(r));
            auto it = std::find(ignore_it, parent.ignored.end(), r);
            if (it != parent.ignored.end()) {
                ignore.emplace_hint(ignore.end(), new_matr.n_rows());
                ignore_it = it;
                ++ignore_it;
            }
        }
    }

    parent.eliminators.clear();

    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().node(new_matr.n_rows()));
    return Node(new_matr, new_cols, ignore);
}


bool FMplexQE::is_positive_combination(const Row& row) {
    assert(row.front().col_index <= delta_column());
    // don't need to check for it == end because the constraint cannot be trivially true here
    for (auto it = row.rbegin(); it->col_index > delta_column(); ++it) {
        if (it->value < 0) return false;
    }
    return true;
}


Node FMplexQE::bounded_elimination(Node& parent) {
    assert(parent.type == Node::Type::LBS || parent.type == Node::Type::UBS);
    assert(!parent.eliminators.empty());

    // remove chosen variable from elimination variables
    auto new_cols = parent.cols_to_elim;
    new_cols.erase(std::find(new_cols.begin(), new_cols.end(), parent.chosen_col));

    // set up new matrix
    Matrix new_matr(parent.matrix.n_rows() - 1, parent.matrix.n_cols());
    new_matr.reserve(parent.matrix.non_zeros_total()); // likely an overapproximation

    // eliminate using eliminator
    RowIndex eliminator = parent.eliminators.back();
    Rational elim_coeff = parent.matrix.coeff(eliminator, parent.chosen_col);
    Rational elim_sgn = (parent.type == Node::Type::LBS ? Rational(1) : Rational(-1));
    parent.eliminators.pop_back();

    auto col_it = parent.matrix.col_begin(parent.chosen_col);
    auto col_end = parent.matrix.col_end(parent.chosen_col);

    std::set<RowIndex> ignore;
    auto ignore_it = parent.ignored.begin();

    bool local_conflict = false; // TODO: make more elegant
    bool inserted = false;

    auto process_row = [&](RowIndex r) {
        inserted = false;
        Rational scale_elim = elim_sgn*col_it->value;
        Rational scale_r = carl::abs(elim_coeff);
        auto combined_row = parent.matrix.combine(eliminator, scale_elim, r, scale_r);
        qe::util::gcd_normalize(combined_row);

        if (combined_row.front().col_index < m_first_parameter_col) {
            // row still contains quantified variables
            inserted = true;
            new_matr.append_row(combined_row.begin(), combined_row.end());
            return true;
        }

        // all quantified variables are eliminated in this row
        // add to overall result or analyze trivial constraint
        if (is_trivial(combined_row)) {
            if (is_conflict(combined_row)) {
                if (is_positive_combination(combined_row)) return false;
                else local_conflict = true;
            }
        } else if (is_positive_combination(combined_row)) {
            m_found_conjuncts.insert(constraint_from_row(combined_row));
            m_found_rows.insert(combined_row);
        }

        return true;
    };

    for (RowIndex r = 0; r < eliminator; ++r) {
        if (r == col_it.row()) {
            if (!process_row(r)) return Node::conflict();
            ++col_it;
        } else {
            inserted = true;
            new_matr.append_row(parent.matrix.row_begin(r), parent.matrix.row_end(r));
        }
        if (ignore_it != parent.ignored.end() && r == *ignore_it) {
            if (inserted) ignore.insert(new_matr.n_rows() - 1);
            ++ignore_it;
        }
    }
    ++col_it;
    for (RowIndex r = eliminator + 1; r < parent.matrix.n_rows(); ++r) {
        if ((col_it != col_end) && (r == col_it.row())) {
            if (!process_row(r)) return Node::conflict();
            ++col_it;
        } else {
            inserted = true;
            new_matr.append_row(parent.matrix.row_begin(r), parent.matrix.row_end(r));
        }
        if (ignore_it != parent.ignored.end() && r == *ignore_it) {
            if (inserted) ignore.insert(new_matr.n_rows() - 1);
            ++ignore_it;
        }
    }

    parent.ignored.insert(eliminator);
    
    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().node(new_matr.n_rows()));
    if (local_conflict) return Node::leaf();
    return Node(new_matr, new_cols, ignore);
}


bool FMplexQE::fm_elimination(Node& parent) {
    parent.eliminators.clear();
    std::vector<RowIndex> lbs, ubs;
    // we can ignore non-bounds since they would have been added to the result at this point
    auto col_it  = parent.matrix.col_begin(parent.chosen_col);
    auto col_end = parent.matrix.col_end(parent.chosen_col);
    for (; col_it != col_end; ++col_it) {
        if (col_it->value < 0) lbs.push_back(col_it.row());
        else ubs.push_back(col_it.row());
    }

    SMTRAT_STATISTICS_CALL(FMplexQEStatistics::get_instance().node(lbs.size() * ubs.size()));

    for (const RowIndex l : lbs) {
        Rational coeff_l = (-1)*parent.matrix.coeff(l, parent.chosen_col);
        for (const RowIndex u : ubs) {
            Rational coeff_u = parent.matrix.coeff(u, parent.chosen_col);
            auto combined_row = parent.matrix.combine(l, coeff_u, u, coeff_l);
            qe::util::gcd_normalize(combined_row);
            if (is_trivial(combined_row)) {
                if (is_global_conflict(combined_row)) return false;
            } else if (is_positive_combination(combined_row)) {
                m_found_conjuncts.insert(constraint_from_row(combined_row));
                m_found_rows.insert(combined_row);
            }
        }
    }
    return true;
}


void FMplexQE::write_matrix_to_ine(const FMplexQE::Matrix& m, const std::string& filename) const {
    std::ofstream file;
    file.open(filename); // "/home/vp/Code/smtrat/build/out.ine"
    file << "H-representation\n";
    file << "begin\n";
    file << m.n_rows() << "  " << m_var_idx.size() + 1 << "  real\n";
    for (RowIndex i = 0; i < m.n_rows(); ++i) {
        Rational lcm = 1;
        Rational constant = 0;
        for (const auto& e : m.row_entries(i)) {
            lcm = carl::lcm(lcm.get_num(), e.value.get_den());
            if (e.col_index == constant_column()) constant = e.value;
        }
        file << "  " << constant*(-lcm); // first column contains the constants
        auto it = m.row_begin(i);
        auto row_end = m.row_end(i);
        for (ColIndex j = 0; j < m_var_idx.size(); ++j) {
            if ((it != row_end) && (it->col_index == j)) {
                file << "  " << (it->value)*(-lcm); // - because cdd uses >= instead of <=
                ++it;
            } else {
                file << "  0";
            }
        }
        file << "\n";
    }
    file << "end\n";
    file << "project " << m_first_parameter_col;
    for (std::size_t i = 1; i <= m_first_parameter_col; ++i) {
        file << " " << i;
    }
    file << "\n";
    file.close();
}

void FMplexQE::write_matrix_to_redlog(const Matrix& m, const std::string& filename) const {
    std::ofstream file;
    file.open(filename); //"/home/vp/Code/smtrat/build/out.red"
    file << "load_package \"redlog\"$\n";
    file << "rlset r$\n";
    file << "rlqe(ex({x1";
    for (std::size_t i = 2; i <= m_first_parameter_col; ++i) {
        file << ", x" << i;
    }
    file << "}, ";

    auto write_row = [&](RowIndex i){
        bool first = true;
        for (const auto& e : m.row_entries(i)) {
            if (e.col_index > constant_column()) break;
            file << " ";
            if (first) first = false;
            else if (e.value > 0) file << "+ ";
            file << e.value;
            if (e.col_index < constant_column()) file << "x" << (e.col_index + 1);
        }
        file << " <= 0";
    };

    write_row(0);
    for (RowIndex i = 1; i < m.n_rows(); ++i) {
        file << " and ";
        write_row(i);
    }

    file << "));\n";
    file << "bye;";
    file.close();
}

} // namespace smtrat::qe::fmplex