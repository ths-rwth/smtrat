#include "fmplex.h"

namespace smtrat::fmplex {

Node FMplexElimination::unbounded_elimination(Node& parent) {
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

    return Node(new_matr, new_cols, ignore);
}


Node FMplexElimination::bounded_elimination(Node& parent) {
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
        gcd_normalize(combined_row);

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
            collect_constraint(combined_row);
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
    
    if (local_conflict) return Node::leaf();
    return Node(new_matr, new_cols, ignore);
}


bool FMplexElimination::fm_elimination(Node& parent) {
    parent.eliminators.clear();
    std::vector<RowIndex> lbs, ubs;
    // we can ignore non-bounds since they would have been added to the result at this point
    auto col_it  = parent.matrix.col_begin(parent.chosen_col);
    auto col_end = parent.matrix.col_end(parent.chosen_col);
    for (; col_it != col_end; ++col_it) {
        if (col_it->value < 0) lbs.push_back(col_it.row());
        else ubs.push_back(col_it.row());
    }

    for (const RowIndex l : lbs) {
        Rational coeff_l = (-1)*parent.matrix.coeff(l, parent.chosen_col);
        for (const RowIndex u : ubs) {
            Rational coeff_u = parent.matrix.coeff(u, parent.chosen_col);
            auto combined_row = parent.matrix.combine(l, coeff_u, u, coeff_l);
            gcd_normalize(combined_row);
            if (is_trivial(combined_row)) {
                if (is_global_conflict(combined_row)) return false;
            } else if (is_positive_combination(combined_row)) {
                collect_constraint(combined_row);
            }
        }
    }
    return true;
}


std::vector<Node> FMplexElimination::split_into_independent_nodes(const Node& n) const {
    const Matrix& m = n.matrix;
    std::vector<bool> col_used(n.cols_to_elim.size(), false);
    std::vector<bool> row_used(m.n_rows(), false);
    std::size_t n_unused_rows = m.n_rows();
    
    std::vector<std::size_t> pending;
    std::vector<Node> result;

    for (std::size_t root_col = 0; root_col < n.cols_to_elim.size();) {
        pending.push_back(root_col);
        result.push_back(Node(Matrix(n_unused_rows, m.n_cols()), {}));
        ++root_col;
        while (!pending.empty()) {
            std::size_t cur_col = pending.back();
            pending.pop_back();

            if (col_used[cur_col]) continue;
            col_used[cur_col] = true;

            ColIndex c = n.cols_to_elim[cur_col];
            result.back().cols_to_elim.push_back(c);

            for (auto it = m.col_begin(c), col_end = m.col_end(c); it != col_end; ++it) {
                if (row_used[it.row()]) continue;
                for (const auto& e : m.row_entries(it.row())) {
                    if (e.col_index >= m_first_parameter_col) break;
                    if (e.col_index == c) continue;
                    for (std::size_t j = 0; ; ++j) {
                        assert(j < n.cols_to_elim.size());
                        if (n.cols_to_elim[j] == e.col_index) {
                            pending.push_back(j);
                            break;
                        }
                    }
                }
                row_used[it.row()] = true;
                --n_unused_rows;
                if (n.ignored.count(it.row()) > 0) {
                    result.back().ignored.insert(result.back().matrix.n_rows());
                }
                result.back().matrix.append_row(m.row_begin(it.row()), m.row_end(it.row()));
            }
        }
        // find next column that is not yet covered
        while (root_col < n.cols_to_elim.size() && col_used[root_col]) ++root_col;
    }
    for (Node& n : result) n.choose_elimination();
    return result;
}

}