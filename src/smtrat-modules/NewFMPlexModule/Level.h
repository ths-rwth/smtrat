#pragma once
#include <eigen3/Eigen/Sparse>
#include "Tableau.h"

namespace smtrat::fmplex {

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

inline DeltaRational choose_value_above(const DeltaRational& bound) {
    return DeltaRational(carl::ceil(bound.mainPart()) + Rational(1), Rational(0));
}

inline DeltaRational choose_value_below(const DeltaRational& bound) {
    return DeltaRational(carl::floor(bound.mainPart()) - Rational(1), Rational(0));
}

inline DeltaRational choose_value_between(const DeltaRational& lower_bound, const DeltaRational& upper_bound) {
    if (lower_bound == upper_bound) return lower_bound;
    RationalInterval range(lower_bound.mainPart(), upper_bound.mainPart()); // REVIEW: is this correct?
    return DeltaRational(carl::sample(range, false), Rational(0));
}

class Level {

    private:
        std::size_t m_level;        /// the actual level
        FMPlexTableau m_tableau;    ///

        std::vector<std::size_t> m_backtrack_levels;    ///
        std::set<RowIndex> m_ignore_for_eliminators;    ///

        std::map<ColumnIndex,Column>::const_iterator m_eliminated_column;   ///
        EliminationType m_elimination_type;                                 ///

        std::vector<std::size_t> m_tried_rows;      /// Indicates which of the tableau's rows have been tried as eliminators.
        std::vector<Eliminator> m_open_eliminators; /// Indicates which of the tableau's rows can still be tried as eliminators.

        std::set<std::size_t> m_unsat_core; /// The **original** rows that make the so far visited children UNSAT.
        bool m_finished = false;            /// Flag indicating whether all children were constructed.
    
    public:
        // Constructors
        Level(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index);

        Level(std::size_t n_constraints, std::size_t level, ColumnIndex rhs_index);

        Level(const FMPlexTableau& tableau);

        // todo: destructor?

        template<bool IgnoreUsed, VariableHeuristic VH>
        bool choose_elimination_column();

        ColumnIndex eliminated_column_index() const;

        template<bool USE_BT=false, bool IGNORE_USED=false>
        Level next_child();

        std::optional<Rational> assign_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const;

        std::optional<Conflict> earliest_conflict(const std::unordered_set<std::size_t>& strict_origins) const;

        void add_to_unsat_core(const std::set<std::size_t>& child_unsat_core);

        inline std::set<std::size_t> unsat_core() const { return m_unsat_core; }

        inline bool finished() const { return m_finished; }

        inline bool is_lhs_zero() const { return m_tableau.is_lhs_zero(); }

    private:

        template<bool IgnoreUsed>
        void collect_eliminators();

        template<bool IgnoreUsed>
        bool choose_elimination_column_column_order();

        // REVIEW: fix encapsulation!
        template<bool IgnoreUsed>
        bool choose_elimination_column_least_branches();

        template<bool USE_BT, bool IGNORE_USED> 
        Level eliminate(const Eliminator& e) const;

        template<bool UseBT, bool IgnoreUsed> 
        Level eliminate_without_bounds() const;
};

Level::Level(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index)
: m_tableau(constraints, variable_index),
  m_backtrack_levels(constraints.size(), 0) {} // todo: duplicates/redundancies?

Level::Level(std::size_t n_constraints, std::size_t level, ColumnIndex rhs_index) 
: m_level(level),
  m_tableau(n_constraints, rhs_index),
  m_backtrack_levels(n_constraints, 0) {}

Level::Level(const FMPlexTableau& tableau) : m_tableau(tableau), m_backtrack_levels(tableau.nr_of_rows(), 0) {} // REVIEW: dont want to copy

template<bool USE_BT, bool IGNORE_USED> 
Level Level::eliminate(const Eliminator& e) const { // REVIEW: watch out for map access, dont use it if possible
    std::cout << "in eliminate\n";
    Level result(m_tableau.nr_of_rows() - 1, m_level + 1, m_tableau.rhs_index());
    Column::const_iterator col_it = m_eliminated_column->second.begin();
    std::vector<std::size_t> new_backtrack_levels;
    new_backtrack_levels.reserve(m_tableau.nr_of_rows() - 1); // TODO: remove at compile time if possible
    std::set<RowIndex> new_ignored; // TODO: remove at compile time if possible

    auto process_row = [&](const RowIndex i, const RowIndex output_row) {
        if (i == col_it->row) {
            auto [row, same_bound]= m_tableau.combine(e.row, i, m_eliminated_column->first, e.coeff, m_tableau.value_at(*col_it));
            result.m_tableau.append_row(row);
            if constexpr (USE_BT) {
                if (same_bound) new_backtrack_levels.push_back(m_level + 1);
                else new_backtrack_levels.push_back(std::max(m_backtrack_levels[e.row], m_backtrack_levels[i]));
            }
            col_it++;
        } else {
            result.m_tableau.copy_row_from(i, m_tableau); // REVIEW: shared pointer so that if tableaus share the same constraint, it is only stored once?
            if constexpr (USE_BT) new_backtrack_levels.push_back(m_backtrack_levels[i]);
        }
        if constexpr (IGNORE_USED) {
            if (m_ignore_for_eliminators.count(i) == 1) {
                new_ignored.emplace_hint(new_ignored.end(), output_row);
            }
        }
    };

    for (RowIndex i = 0; i < e.row; i++) {// Requires the column index elements to be in ascending order!!
        process_row(i,i);
    }
    col_it++; // should point to pivot_row before this increment
    for (RowIndex i = e.row + 1; i < m_tableau.nr_of_rows(); i++) {
        process_row(i,i-1);
    }
    result.m_backtrack_levels = new_backtrack_levels;
    result.m_ignore_for_eliminators = new_ignored;
    return result;
}

template<bool UseBT, bool IgnoreUsed> 
Level Level::eliminate_without_bounds() const {
    std::cout << "in eliminate\n";
    Level result(m_tableau.nr_of_rows() - m_eliminated_column->second.size(), m_level + 1, m_tableau.rhs_index());
    std::vector<std::size_t> new_backtrack_levels;
    new_backtrack_levels.reserve(m_tableau.nr_of_rows() - 1);
    std::set<RowIndex> new_ignored;
    RowIndex added_row = 0;
    Column::const_iterator col_it = m_eliminated_column->second.begin();
    for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
        if (i == col_it->row) { // Requires the column elements to be in ascending order!!
            col_it++;
        } else {
            result.m_tableau.copy_row_from(i, m_tableau);
            if constexpr (UseBT) new_backtrack_levels.push_back(m_backtrack_levels[i]);
            if constexpr (IgnoreUsed) {
                if (m_ignore_for_eliminators.count(i) == 1) new_ignored.emplace_hint(new_ignored.end(), added_row);
                added_row++;
            }
        }
    }
    result.m_backtrack_levels = new_backtrack_levels; // REVIEW: avoid this copy, and: encapsulation
    result.m_ignore_for_eliminators = new_ignored;
    return result;
}

template<bool IgnoreUsed, VariableHeuristic VH>
bool Level::choose_elimination_column() {
    std::cout << "in choosevar\n";
    if constexpr (VH == VariableHeuristic::COLUMN_ORDER) {
        return choose_elimination_column_column_order<IgnoreUsed>();
    }   
    if constexpr (VH == VariableHeuristic::LEAST_BRANCHES) {
        return choose_elimination_column_least_branches<IgnoreUsed>();
    }
    assert(false); // unreachable
    return false;
}

template<bool IgnoreUsed>
void Level::collect_eliminators() {
    bool collect_lbs = (m_elimination_type == EliminationType::LBS);
    for (const auto& col_elem : m_eliminated_column->second) {
        if constexpr (IgnoreUsed) {
            if (m_ignore_for_eliminators.count(col_elem.row) == 1) continue;
        }
        Rational val = m_tableau.value_at(col_elem);
        std::cout << "val < 0 == collect lbs: " << ((val < 0) == collect_lbs) << "\n";
        if ((val < 0) == collect_lbs) m_open_eliminators.emplace_back(col_elem.row, val);
    }
}

template<bool IgnoreUsed>
bool Level::choose_elimination_column_column_order() {
    auto col_it = m_tableau.columns_begin();
    if (col_it->first >= m_tableau.rhs_index()) return false;
    std::size_t n_lbs = 0, n_ubs = 0;
    std::size_t n_ignored_lbs = 0, n_ignored_ubs = 0;
    for (const auto& col_elem : col_it->second) {
        if (m_tableau.value_at(col_elem) > 0) {
            n_ubs++;
            if constexpr (IgnoreUsed) {
                if (m_ignore_for_eliminators.count(col_elem.row) == 1) n_ignored_ubs++;
            }
        } else {
            n_lbs++;
            if constexpr (IgnoreUsed) {
                if (m_ignore_for_eliminators.count(col_elem.row) == 1) n_ignored_lbs++;
            }
        }
    }
    if constexpr (IgnoreUsed) {
        if ((n_ignored_lbs == n_lbs) || (n_ignored_ubs == n_ubs)) return false; // UNSAT
        n_lbs -= n_ignored_lbs;
        n_ubs -= n_ignored_ubs;
    }
    m_eliminated_column = col_it;
    if ((n_lbs == 0) || (n_ubs == 0)) m_elimination_type = EliminationType::NONE;
    else if (n_lbs <= n_ubs) m_elimination_type = EliminationType::LBS;
    else m_elimination_type = EliminationType::UBS;

    collect_eliminators<IgnoreUsed>();
    std::cout << "eliminated column: " << m_eliminated_column->first << "\n";
    return true;
}

// REVIEW: fix encapsulation!
template<bool IgnoreUsed>
bool Level::choose_elimination_column_least_branches() {
    std::optional<size_t> fewest_branches;

    for (auto col_it = m_tableau.columns_begin(); col_it != m_tableau.columns_end(); col_it++) {
        // We only consider the columns corresponding to the original variables
        if (col_it->first >= m_tableau.rhs_index()) break;

        std::size_t n_lbs = 0, n_ubs = 0;
        std::size_t n_ignored_lbs = 0, n_ignored_ubs = 0;
        for (const auto& col_elem : col_it->second) {
            if (m_tableau.value_at(col_elem) > 0) {
                n_ubs++;
                if constexpr (IgnoreUsed) {
                    if (m_ignore_for_eliminators.count(col_elem.row) == 1) n_ignored_ubs++;
                }
            } else {
                n_lbs++;
                if constexpr (IgnoreUsed) {
                    if (m_ignore_for_eliminators.count(col_elem.row) == 1) n_ignored_lbs++;
                }
            }
        }
        if constexpr (IgnoreUsed) {
            if ((n_ignored_lbs == n_lbs) || (n_ignored_ubs == n_ubs)) return false; // UNSAT
            n_lbs -= n_ignored_lbs;
            n_ubs -= n_ignored_ubs;
        }
        if (n_lbs == 0 || n_ubs == 0) {
            m_eliminated_column = col_it;
            m_elimination_type = EliminationType::NONE;
            return true;
        }
        if (n_lbs <= n_ubs) {
            if (!fewest_branches || (n_lbs < (*fewest_branches))) {
                fewest_branches = n_lbs;
                m_eliminated_column = col_it;
                m_elimination_type = EliminationType::LBS;
            } 
        } else if (!fewest_branches || (n_ubs < (*fewest_branches))) {
            fewest_branches = n_ubs;
            m_eliminated_column = col_it;
            m_elimination_type = EliminationType::UBS;
        }
    }

    assert(fewest_branches.has_value());
    collect_eliminators<IgnoreUsed>();
    return true;
}

ColumnIndex Level::eliminated_column_index() const {
    return m_eliminated_column->first;
}

template<bool USE_BT, bool IGNORE_USED>
Level Level::next_child() {
    std::cout << "in next_child\n";
    // todo: ignore pivots optimization
    if (m_elimination_type == EliminationType::NONE) {
        m_finished = true;
        std::cout << "eliminating wo buonds\n";
        return eliminate_without_bounds<USE_BT,IGNORE_USED>();
    } else { // todo: eliminator choice heuristic
        Eliminator e = m_open_eliminators.back();
        m_open_eliminators.pop_back();
        std::cout << "eliminating\n";
        Level child = eliminate<USE_BT,IGNORE_USED>(e);
        m_tried_rows.push_back(e.row);
        if constexpr (IGNORE_USED) {
            m_ignore_for_eliminators.emplace(e.row);
        }
        if (m_open_eliminators.empty()) m_finished = true;
        std::cout << "leaving next_child\n";
        return child;
    }
}

std::optional<Rational> Level::assign_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const {
    // todo: can use heuristics and optimize if only weak bounds are present

    // set implicitly eliminated variables to zero
    std::vector<ColumnIndex> non_zero_variable_columns = m_tableau.non_zero_variable_columns();
    for (const auto col : non_zero_variable_columns) {
        if (col == m_eliminated_column->first) continue;
        if (m.count(col) == 0) m.emplace(col, DeltaRational(0)); // REVIEW: better with lower_bound?
    }

    auto col_it = m_eliminated_column->second.begin();
    std::optional<DeltaRational> lower_bound, upper_bound;

    std::cout << "assigning " << m_eliminated_column->first << "\n";

    switch (m_elimination_type) {
        case EliminationType::NONE:
            if (m_tableau.value_at(*col_it) > 0) {
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!upper_bound || (bound < (*upper_bound))) {
                        upper_bound = bound;
                    }
                }
                m.emplace(m_eliminated_column->first, choose_value_below(*upper_bound));
                return std::nullopt;
            } else {
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!lower_bound || (bound > (*lower_bound))) {
                        lower_bound = bound;
                    }
                }
                m.emplace(m_eliminated_column->first, choose_value_above(*lower_bound));
                return std::nullopt;
            }
            break;
        case EliminationType::LBS:
            for (; col_it != m_eliminated_column->second.end(); col_it++) {
                if (col_it->row == m_tried_rows.back()) {
                    lower_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                } else if (m_tableau.value_at(*col_it) > 0){
                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!upper_bound || (bound < (*upper_bound))) {
                        upper_bound = bound;
                    }
                }
            }
            break;
        case EliminationType::UBS:
            for (; col_it != m_eliminated_column->second.end(); col_it++) {
                if (col_it->row == m_tried_rows.back()) {
                    upper_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                } else if (m_tableau.value_at(*col_it) < 0){
                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!lower_bound || (bound > (*lower_bound))) {
                        lower_bound = bound;
                    }
                }
            }
            break;
        default: // unreachable
            assert(false);
            return std::nullopt;
    }
    assert(lower_bound.has_value() && upper_bound.has_value());
    std::cout << "lb: " << (*lower_bound) << ", ub: " << (*upper_bound) << "\n";
    m.emplace(m_eliminated_column->first, choose_value_between(*lower_bound, *upper_bound));
    if (lower_bound->deltaPart() > upper_bound->deltaPart()) {
        return (upper_bound->mainPart() - lower_bound->mainPart()) / (lower_bound->deltaPart() - upper_bound->deltaPart());
    }
    return std::nullopt;
}

std::optional<Conflict> Level::earliest_conflict(const std::unordered_set<std::size_t>& strict_origins) const {
    std::optional<Conflict> result;
    for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
        if (m_tableau.is_row_conflict(i)) {
            Origins ogs = m_tableau.origins(i);
            if (ogs.non_negative) return Conflict{0, ogs.constraint_indices};
            if (!result || (m_backtrack_levels[i] < result->level)) {
                result = Conflict{m_backtrack_levels[i], ogs.constraint_indices};
            }
        }
    }
    return result;
}

void Level::add_to_unsat_core(const std::set<std::size_t>& child_unsat_core) {
    m_unsat_core.insert(child_unsat_core.begin(), child_unsat_core.end());
}

} // namespace smtrat::fmplex