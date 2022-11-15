#include <eigen3/Eigen/Sparse>

namespace smtrat {
    namespace fmplex {

        using ColumnIndex = std::size_t;
        using RowIndex = std::size_t;
        using ColumnPosition = std::size_t;

        struct RowElement {
            ColumnIndex column;
            Rational value;
            RowElement(const ColumnIndex c, const Rational& v) : column(c), value(v) {}
        };

        struct Row {
            std::vector<RowElement> elements;
            carl::Relation relation;
            std::size_t backtrack_level;
        };

        struct Eliminator {
            RowIndex row;
            Rational coeff; // TODO: as reference?
            Eliminator(const RowIndex r, const Rational& c) : row(r), coeff(c) {}
        };

        struct ColumnElement {
            RowIndex row;
            ColumnPosition position_in_row;
            ColumnElement(const RowIndex r, const ColumnPosition p) : row(r), position_in_row(p) {}
        };

        using Column = std::vector<ColumnElement>;

        enum class EliminationType {
            LBS, UBS, NONE
        };

        struct Conflict {
            std::size_t level;
            std::set<std::size_t> involved_rows;
        };

        class FMPlexTableau { // TODO: memory management : alle RowElements in einen grossen vector?
            private:
                /// vector containing the rows
                std::vector<Row> m_rows;
                /// number of rows
                std::size_t m_nr_rows;
                /// map containing the non-zero columns
                std::map<ColumnIndex,Column> m_columns;
                /// the level of this tableau
                std::size_t m_level;

                std::size_t m_rhs_index;
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
                FMPlexTableau(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) { // TODO: duplicates/redundancies?
                    m_rows.reserve(constraints.size());
                    m_nr_rows = constraints.size();
                    m_rhs_index = variable_index.size();
                    
                    for (std::size_t row = 0; row < constraints.size(); row++) {
                        Row current_row;
                        const FormulaT& c = constraints[row];
                        carl::Relation r = c.constraint().relation();
                        current_row.relation = (carl::is_weak(r) ? carl::Relation::LEQ : carl::Relation::LESS);
                        current_row.backtrack_level = 0;
                        Poly p = c.constraint().lhs();
                        current_row.elements.reserve(p.nr_terms()+1);
                        if (r == carl::Relation::GEQ || r == carl::Relation::GREATER) {
                            for (const auto& term : p) {
                                std::size_t column = term.is_constant() ? m_rhs_index : variable_index.at(term.single_variable());
                                current_row.elements.emplace_back(column, -term.coeff());
                            }
                        } else { // r == LEQ or r == LESS
                            for (const auto& term : p) {
                                std::size_t column = term.is_constant() ? m_rhs_index : variable_index.at(term.single_variable());
                                current_row.elements.emplace_back(column, -term.coeff());
                            }
                        }
                        current_row.elements.emplace_back(m_rhs_index + row, Rational(1));
                        append_row(current_row);
                    }
                }



                FMPlexTableau(std::size_t n_rows, std::size_t level, ColumnIndex rhs_index) {
                    m_rows.reserve(n_rows);
                    m_level = level;
                    m_rhs_index = rhs_index;
                    m_nr_rows = n_rows;
                }

                void append_row(const Row& row) {
                    for (ColumnPosition i = 0; i < row.elements.size(); i++) {
                        RowElement r = row.elements[i];
                        // TODO: the same could be achieved by calling m_columns.insert({r.column, std::vector<ColumnElement>()}); without lower_bound
                        auto it = m_columns.lower_bound(r.column);
                        if ((it == m_columns.end()) || (it->first != r.column)) {
                            it = m_columns.insert(it, {r.column, std::vector<ColumnElement>()});
                        }
                        it->second.emplace_back(m_rows.size(), i);
                    }
                    m_rows.push_back(row);
                }

                Row combine(const Row& pivot_row, const Row& other_row, ColumnIndex eliminated, const Rational& pivot_coeff, const Rational& other_coeff) {
                    Row result;
                    result.elements.reserve(m_columns.size()-1); // TODO: or minimum with pivot.size+other.size?
                    Rational pivot_scale;
                    Rational other_scale;
                    result.backtrack_level = std::max(pivot_row.backtrack_level, other_row.backtrack_level);
                    // TODO: durch delta Zeug ersetzen?
                    if (pivot_row.relation == carl::Relation::LEQ) {
                        result.relation = other_row.relation;
                    } else if (((pivot_coeff > 0) && (other_coeff > 0)) || ((pivot_coeff < 0) && (other_coeff < 0))) {
                        result.relation = carl::Relation::LEQ;
                    } else {
                        result.relation = carl::Relation::LESS;
                    }
                    // TODO: skalierung anpassen? Nur mit Integers arbeiten?
                    if (pivot_coeff > 0) {
                        pivot_scale = -other_coeff;
                        other_scale = pivot_coeff;
                        if (other_coeff > 0) {
                            result.backtrack_level = m_level + 1;
                        }
                    } else { // pivot_coeff < 0
                        pivot_scale = other_coeff;
                        other_scale = -pivot_coeff;
                        if (other_coeff < 0) {
                            result.backtrack_level = m_level + 1;
                        }
                    }

                    std::vector<RowElement>::const_iterator pivot_iter = pivot_row.elements.begin();
                    std::vector<RowElement>::const_iterator other_iter = other_row.elements.begin();
                    std::vector<RowElement>::const_iterator pivot_end = pivot_row.elements.end();
                    std::vector<RowElement>::const_iterator other_end = other_row.elements.end();
                    while((pivot_iter != pivot_end) && (other_iter != other_end)) {
                        if (pivot_iter->column < other_iter->column) {
                            result.elements.emplace_back(pivot_iter->column, pivot_scale*(pivot_iter->value));
                            pivot_iter++;
                        } else if (pivot_iter->column > other_iter->column) {
                            result.elements.emplace_back(other_iter->column, other_scale*(other_iter->value));
                            other_iter++;
                        } else { // same column
                            if (pivot_iter->column != m_eliminated_column->first) { // we know that the eliminated colum will be zero
                                Rational value = other_scale*(other_iter->value) + pivot_scale*(pivot_iter->value);
                                if (!carl::is_zero(value)) result.elements.emplace_back(pivot_iter->column, value);
                            }
                            pivot_iter++;
                            other_iter++;
                        }
                    }
                }

                FMPlexTableau eliminate(const std::vector<Row>::const_iterator& pivot_row_it, const Rational& pivot_coeff) { // TODO: watch out for map access, dont use it if possible
                    FMPlexTableau result(m_nr_rows - 1, m_level + 1, m_rhs_index);
                    Column::const_iterator col_it = m_eliminated_column->second.begin();
                    std::vector<Row>::const_iterator it = m_rows.begin();
                    for (; it != pivot_row_it; it++) {
                        // Requires the column index elements to be in ascending order!!
                        if (it == m_rows.begin() + col_it->row) { // TODO: this code is not nice
                            result.append_row(combine(*pivot_row_it, *it, m_eliminated_column->first, pivot_coeff, it->elements[col_it->position_in_row].value));
                            col_it++;
                        } else {
                            result.append_row(*it);
                        }
                    }
                    col_it++; // should point to pivot_row before this increment
                    it++;
                    for (; it != m_rows.end(); it++) {
                        // Requires the column elements to be in ascending order!!
                        if (it == m_rows.begin() + col_it->row) { // TODO: this code is not nice
                            result.append_row(combine(*pivot_row_it, *it, m_eliminated_column->first, pivot_coeff, it->elements[col_it->position_in_row].value));
                            col_it++;
                        } else {
                            result.append_row(*it);
                        }
                    }
                    return result;
                }

                FMPlexTableau eliminate_without_bounds() {
                    FMPlexTableau result(m_nr_rows - 1, m_level + 1, m_rhs_index);
                    Column::const_iterator col_it = m_eliminated_column->second.begin();
                    for (RowIndex i = 0; i < m_rows.size(); i++) {
                        if (i == col_it->row) { // Requires the column elements to be in ascending order!!
                            col_it++;
                        } else {
                            result.append_row(m_rows[i]);
                        }
                    }
                    return result;
                }

                ColumnIndex choose_elimination_column() { // assumes that there still are eliminable columns
                    std::optional<size_t> fewest_branches;

                    for (std::map<ColumnIndex, Column>::const_iterator col_it = m_columns.begin(); col_it != m_columns.end(); col_it++) {
                        // We only consider the columns corresponding to the original variables
                        if (col_it->first >= m_rhs_index) break;

                        std::size_t n_lbs = 0, n_ubs = 0;
                        for (const auto& col_elem : col_it->second) {
                            if (m_rows[col_elem.row].elements[col_elem.position_in_row].value > 0) n_ubs++;
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
                            Rational val = m_rows[col_elem.row].elements[col_elem.position_in_row].value;
                            if (val < 0) m_open_rows.emplace_back(col_elem.row, val);
                        }
                    } else { // m_elimination_type == EliminationType::UBS
                        for (const auto& col_elem : m_eliminated_column->second) {
                            Rational val = m_rows[col_elem.row].elements[col_elem.position_in_row].value;
                            if (val > 0) m_open_rows.emplace_back(col_elem.row, val);
                        }
                    }
                    return m_eliminated_column->first;
                }

                ColumnIndex eliminated_column_index() const {
                    return m_eliminated_column->first;
                }

                FMPlexTableau next_child() {
                    // TODO: ignore pivots optimization
                    if (m_elimination_type == EliminationType::NONE) {
                        m_finished = true;
                        return eliminate_without_bounds();
                    } else { // TODO: eliminator choice heuristic
                        Eliminator e = m_open_rows.back();
                        FMPlexTableau child = eliminate(m_rows.begin() + e.row, e.coeff);
                        m_tried_rows.push_back(e.row);
                        m_open_rows.pop_back();
                        if (m_open_rows.empty()) m_finished = true;
                        return child;
                    }
                }

                Rational bound_value(const Row& row, const std::map<std::size_t, Rational>& m) const {
                    Rational bound(0);
                    Rational coeff;
                    for (const auto& row_elem : row.elements) {
                        if (row_elem.column > m_rhs_index) break;
                        else if (row_elem.column == m_rhs_index) bound = bound + row_elem.value;
                        else if (row_elem.column != m_eliminated_column->first) bound = bound - (row_elem.value * m.at(row_elem.column));
                        else coeff = row_elem.value;
                    }
                    bound = bound / coeff;
                    return bound;
                }

                Rational find_variable_assignment(const std::map<std::size_t, Rational>& m) const {
                    // TODO: can use heuristics and optimize if only weak bounds are present
                    auto col_it = m_eliminated_column->second.begin();
                    std::optional<Rational> lower_bound, upper_bound;
                    carl::Relation lower_rel, upper_rel;
                    switch (m_elimination_type) {
                        case EliminationType::NONE:
                            if (m_rows[col_it->row].elements[col_it->position_in_row].value > 0) {
                                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                    Rational bound = bound_value(m_rows[col_it->row], m);
                                    if (!upper_bound || (bound < (*upper_bound))) {
                                        upper_bound = bound;
                                    }
                                }
                                return carl::floor((*upper_bound) - Rational(1));
                            } else {
                                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                    Rational bound = bound_value(m_rows[col_it->row], m);
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
                                    lower_bound = bound_value(m_rows[col_it->row], m);
                                    lower_rel = m_rows[col_it->row].relation;
                                } else if (m_rows[col_it->row].elements[col_it->position_in_row].value > 0){
                                    Rational bound = bound_value(m_rows[col_it->row], m);
                                    if (!upper_bound || (bound < (*upper_bound))) {
                                        upper_bound = bound;
                                        upper_rel = m_rows[col_it->row].relation;
                                    } else if ((upper_rel == carl::Relation::LEQ) && (m_rows[col_it->row].relation == carl::Relation::LESS)) {
                                        if (bound == (*upper_bound)) {
                                            upper_bound = bound;
                                            upper_rel = m_rows[col_it->row].relation;
                                        }
                                    }
                                }
                            }
                            break;
                        case EliminationType::UBS:
                            for (; col_it != m_eliminated_column->second.end(); col_it++) {
                                if (col_it->row == m_tried_rows.back()) {
                                    upper_bound = bound_value(m_rows[col_it->row], m);
                                    upper_rel = m_rows[col_it->row].relation;
                                } else if (m_rows[col_it->row].elements[col_it->position_in_row].value < 0){
                                    Rational bound = bound_value(m_rows[col_it->row], m);
                                    if (!lower_bound || (bound < (*lower_bound))) {
                                        lower_bound = bound;
                                        lower_rel = m_rows[col_it->row].relation;
                                    } else if ((lower_rel == carl::Relation::LEQ) && (m_rows[col_it->row].relation == carl::Relation::LESS)) {
                                        if (bound == (*lower_bound)) {
                                            lower_bound = bound;
                                            lower_rel = m_rows[col_it->row].relation;
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

                std::size_t origin(ColumnIndex ci) {
                    assert(ci > m_rhs_index);
                    return ci - m_rhs_index - 1;
                }

                std::optional<Conflict> earliest_conflict(const std::unordered_set<std::size_t>& strict_origins) {
                    std::optional<Conflict> result;
                    for (const auto& row: m_rows) {
                        auto row_it = row.elements.begin();
                        bool test_strict = false;
                        if (row_it->column < m_rhs_index) continue;
                        else if (row_it->column == m_rhs_index) {
                            if (row_it->value > 0) continue;
                            row_it++;
                        } else if (row.relation == carl::Relation::LEQ) continue;
                        else test_strict = true;

                        if (!result || (row.backtrack_level < result->level)) {
                            bool non_neg = true;
                            bool really_strict = false;
                            std::set<std::size_t> involved;
                            while (row_it != row.elements.end()) {
                                if (row_it->value < 0) non_neg = false;
                                if (test_strict && (strict_origins.count(origin(row_it->column)) == 1)) {
                                    really_strict = true;
                                }
                                involved.insert(origin(row_it->column));
                            }
                            std::size_t level = (!non_neg || (test_strict && !really_strict)) ? row.backtrack_level : 0;
                            result = Conflict{level, involved};
                        }
                    }
                    return result;
                }

                std::set<std::size_t> unsat_core() const { // TODO: return const reference?
                    return m_unsat_core;
                }

                void add_to_unsat_core(const std::set<std::size_t>& child_unsat_core) {
                    m_unsat_core.insert(child_unsat_core.begin(), child_unsat_core.end());
                }

                bool finished() const {
                    return m_finished;
                }

                bool is_lhs_zero() {
                    // if the first non-zero column is the rhs (or one of the lin comb columns)
                    return (m_columns.begin()->first) >= m_rhs_index;
                }
        };

    } // namespace fmplex
} // namespace smtrat