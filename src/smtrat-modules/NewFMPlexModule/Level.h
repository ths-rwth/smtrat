#include <eigen3/Eigen/Sparse>
#include "Tableau.h"

namespace smtrat {
    namespace fmplex {

        struct Eliminator {
            RowIndex row;
            Rational coeff; // REVIEW: as reference?
            Eliminator(const RowIndex r, const Rational& c) : row(r), coeff(c) {}
        };

        enum class EliminationType {
            LBS, UBS, NONE
        };

        struct Conflict {
            std::size_t level;
            std::set<std::size_t> involved_rows;
        };

        class Level {

            private:
                /// the actual level
                std::size_t m_level;
                FMPlexTableau m_tableau;
                std::vector<std::size_t> m_backtrack_levels;
                /// 
                std::map<ColumnIndex,Column>::const_iterator m_eliminated_column;

                /// Indicates which of the tableau's rows have been tried as eliminators
                std::vector<std::size_t> m_tried_rows;
                /// Indicates which of the tableau's rows can still be tried as eliminators. If no rows are used (only one bound type) this is nullopt
                std::vector<Eliminator> m_open_rows;
                /// The **original** rows that make the so far visited children UNSAT
                std::set<std::size_t> m_unsat_core;
                /// Flag indicating whether all children were constructed
                bool m_finished = false;

                EliminationType m_elimination_type;

            public:
                Level(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index)
                : m_tableau(constraints, variable_index),
                  m_backtrack_levels(constraints.size(), 0) {} // todo: duplicates/redundancies?

                Level(std::size_t n_constraints, std::size_t level, ColumnIndex rhs_index) 
                : m_level(level),
                 m_tableau(n_constraints, rhs_index),
                 m_backtrack_levels(n_constraints, 0) {}

                Level(const FMPlexTableau& tableau) : m_tableau(tableau), m_backtrack_levels(tableau.nr_of_rows(), 0) {} // REVIEW: dont want to copy

                Level eliminate(RowIndex pivot_row, const Rational& pivot_coeff) { // REVIEW: watch out for map access, dont use it if possible
                    Level result(m_tableau.nr_of_rows() - 1, m_level + 1, m_tableau.rhs_index());
                    Column::const_iterator col_it = m_eliminated_column->second.begin();
                    std::vector<std::size_t> new_backtrack_levels;
                    new_backtrack_levels.reserve(m_tableau.nr_of_rows() - 1);
                    RowIndex i = 0;
                    for (; i < pivot_row; i++) {
                        // Requires the column index elements to be in ascending order!!
                        if (i == col_it->row) {
                            std::pair<Row,bool> row_reset_level = m_tableau.combine(pivot_row, i, m_eliminated_column->first, pivot_coeff, m_tableau.value_at(*col_it));
                            result.m_tableau.append_row(row_reset_level.first);
                            if (row_reset_level.second) new_backtrack_levels.push_back(m_level + 1);
                            else new_backtrack_levels.push_back(std::max(m_backtrack_levels[pivot_row], m_backtrack_levels[i]));
                            col_it++;
                        } else {
                            result.m_tableau.copy_row_from(i, m_tableau); // REVIEW: shared pointer so that if tableaus share the same constraint, it is only stored once?
                            new_backtrack_levels.push_back(m_backtrack_levels[i]);
                        }
                    }
                    col_it++; // should point to pivot_row before this increment
                    i++;
                    for (; i < m_tableau.nr_of_rows(); i++) {
                        // Requires the column elements to be in ascending order!!
                        if (i == col_it->row) {
                            std::pair<Row,bool> row_reset_level = m_tableau.combine(pivot_row, i, m_eliminated_column->first, pivot_coeff, m_tableau.value_at(*col_it));
                            result.m_tableau.append_row(row_reset_level.first);
                            if (row_reset_level.second) new_backtrack_levels.push_back(m_level + 1);
                            else new_backtrack_levels.push_back(std::max(m_backtrack_levels[pivot_row], m_backtrack_levels[i]));
                            col_it++;
                        } else {
                            result.m_tableau.copy_row_from(i, m_tableau);
                            new_backtrack_levels.push_back(m_backtrack_levels[i]);
                        }
                    }
                    result.m_backtrack_levels = new_backtrack_levels;
                    return result;
                }

                Level eliminate_without_bounds() {
                    Level result(m_tableau.nr_of_rows() - m_eliminated_column->second.size(), m_level + 1, m_tableau.rhs_index());
                    std::vector<std::size_t> new_backtrack_levels;
                    new_backtrack_levels.reserve(m_tableau.nr_of_rows() - 1);
                    Column::const_iterator col_it = m_eliminated_column->second.begin();
                    for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
                        if (i == col_it->row) { // Requires the column elements to be in ascending order!!
                            col_it++;
                        } else {
                            result.m_tableau.copy_row_from(i, m_tableau);
                            new_backtrack_levels.push_back(m_backtrack_levels[i]);
                        }
                    }
                    result.m_backtrack_levels = new_backtrack_levels; // REVIEW: avoid this copy, and: encapsulation
                    return result;
                }

                // TODO: use heuristics
                // REVIEW: fix encapsulation!
                ColumnIndex choose_elimination_column() { // assumes that there still are eliminable columns
                    std::optional<size_t> fewest_branches;

                    for (std::map<ColumnIndex, Column>::const_iterator col_it = m_tableau.columns_begin(); col_it != m_tableau.columns_end(); col_it++) {
                        // We only consider the columns corresponding to the original variables
                        if (col_it->first >= m_tableau.rhs_index()) break;

                        std::size_t n_lbs = 0, n_ubs = 0;
                        for (const auto& col_elem : col_it->second) {
                            if (m_tableau.value_at(col_elem) > 0) n_ubs++;
                            else n_lbs++;
                        }
                        if (n_lbs == 0 || n_ubs == 0) {
                            m_eliminated_column = col_it;
                            m_elimination_type = EliminationType::NONE;
                            return col_it->first;
                        } else if (n_lbs <= n_ubs) {
                            if (!fewest_branches || (n_lbs < (*fewest_branches))) {
                                fewest_branches = n_lbs;
                                m_eliminated_column = col_it;
                                m_elimination_type = EliminationType::LBS;
                            } 
                        } else {
                            if (!fewest_branches || (n_ubs < (*fewest_branches))) {
                                fewest_branches = n_ubs;
                                m_eliminated_column = col_it;
                                m_elimination_type = EliminationType::UBS;
                            } 
                        }
                    }

                    assert(fewest_branches.has_value());

                    if (m_elimination_type == EliminationType::LBS) {
                        for (const auto& col_elem : m_eliminated_column->second) {
                            Rational val = m_tableau.value_at(col_elem);
                            if (val < 0) m_open_rows.emplace_back(col_elem.row, val);
                        }
                    } else { // m_elimination_type == EliminationType::UBS
                        for (const auto& col_elem : m_eliminated_column->second) {
                            Rational val = m_tableau.value_at(col_elem);
                            if (val > 0) m_open_rows.emplace_back(col_elem.row, val);
                        }
                    }
                    return m_eliminated_column->first;
                }

                ColumnIndex eliminated_column_index() const {
                    return m_eliminated_column->first;
                }

                Level next_child() {
                    // todo: ignore pivots optimization
                    if (m_elimination_type == EliminationType::NONE) {
                        m_finished = true;
                        return eliminate_without_bounds();
                    } else { // todo: eliminator choice heuristic
                        Eliminator e = m_open_rows.back();
                        Level child = eliminate(e.row, e.coeff);
                        m_tried_rows.push_back(e.row);
                        m_open_rows.pop_back();
                        if (m_open_rows.empty()) m_finished = true;
                        return child;
                    }
                }

                Rational find_variable_assignment(const std::map<std::size_t, Rational>& m) const {
                    // todo: can use heuristics and optimize if only weak bounds are present
                    auto col_it = m_eliminated_column->second.begin();
                    std::optional<Rational> lower_bound, upper_bound;
                    carl::Relation lower_rel, upper_rel;
                    switch (m_elimination_type) {
                        case EliminationType::NONE:
                            if (m_tableau.value_at(*col_it) > 0) {
                                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                    Rational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    if (!upper_bound || (bound < (*upper_bound))) {
                                        upper_bound = bound;
                                    }
                                }
                                return carl::floor((*upper_bound) - Rational(1));
                            } else {
                                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                    Rational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    if (!lower_bound || (bound > (*upper_bound))) {
                                        upper_bound = bound;
                                    }
                                }
                                return carl::ceil((*upper_bound) + Rational(1));
                            }
                            break;
                        case EliminationType::LBS:
                            for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                if (col_it->row == m_tried_rows.back()) {
                                    lower_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    lower_rel = m_tableau.relation(col_it->row);
                                } else if (m_tableau.value_at(*col_it) > 0){
                                    Rational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    if (!upper_bound || (bound < (*upper_bound))) {
                                        upper_bound = bound;
                                        upper_rel = m_tableau.relation(col_it->row);
                                    } else if ((upper_rel == carl::Relation::LEQ) && (m_tableau.relation(col_it->row) == carl::Relation::LESS)) {
                                        if (bound == (*upper_bound)) {
                                            upper_bound = bound;
                                            upper_rel = m_tableau.relation(col_it->row);
                                        }
                                    }
                                }
                            }
                            break;
                        case EliminationType::UBS:
                            for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                if (col_it->row == m_tried_rows.back()) {
                                    upper_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    upper_rel = m_tableau.relation(col_it->row);
                                } else if (m_tableau.value_at(*col_it) < 0){
                                    Rational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                                    if (!lower_bound || (bound < (*lower_bound))) {
                                        lower_bound = bound;
                                        lower_rel = m_tableau.relation(col_it->row);
                                    } else if ((lower_rel == carl::Relation::LEQ) && (m_tableau.relation(col_it->row) == carl::Relation::LESS)) {
                                        if (bound == (*lower_bound)) {
                                            lower_bound = bound;
                                            lower_rel = m_tableau.relation(col_it->row);
                                        }
                                    }
                                }
                            }
                            break;
                        default: // unreachable
                            assert(false);
                    }
                    assert(lower_bound.has_value() && upper_bound.has_value());
                    if (*lower_bound == *upper_bound) return *lower_bound;
                    RationalInterval range(*lower_bound,*upper_bound);
                    return carl::sample(range, false);
                }

                std::optional<Conflict> earliest_conflict(const std::unordered_set<std::size_t>& strict_origins) {
                    std::optional<Conflict> result;
                    for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
                        auto [conflict, test_strict] = m_tableau.is_row_conflict(i);
                        if (!conflict) continue;
                        if (!result || (m_backtrack_levels[i] < result->level)) {
                            bool really_strict = false;
                            auto [involved, non_neg] = m_tableau.origins(i);
                            for (const std::size_t o : involved) {
                                if (strict_origins.count(o) == 1) {
                                    really_strict = true;
                                    break;
                                }
                            }
                            std::size_t level = (!non_neg || (test_strict && !really_strict)) ? m_backtrack_levels[i] : 0;
                            result = Conflict{level, involved};
                        }
                    }
                    return result;
                }

                std::set<std::size_t> unsat_core() const { // REVIEW: return const reference?
                    return m_unsat_core;
                }

                void add_to_unsat_core(const std::set<std::size_t>& child_unsat_core) {
                    m_unsat_core.insert(child_unsat_core.begin(), child_unsat_core.end());
                }

                bool finished() const {
                    return m_finished;
                }

                bool is_lhs_zero() const {
                    return m_tableau.is_lhs_zero();
                }
        };

    } // namespace fmplex
} // namespace smtrat