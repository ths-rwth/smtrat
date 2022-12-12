#pragma once
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
    bool is_global;
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
    assert(lower_bound <= upper_bound);
    if (lower_bound == upper_bound) return lower_bound;
    if (lower_bound.mainPart() != upper_bound.mainPart()) {
        RationalInterval real_range(lower_bound.mainPart(), upper_bound.mainPart());
        return DeltaRational(carl::sample(real_range, false), Rational(0));
    } // else : same real part
    if ((lower_bound.deltaPart() > 0) == (upper_bound.deltaPart() > 0)) {
        RationalInterval delta_range(lower_bound.deltaPart(), upper_bound.deltaPart());
        return DeltaRational(lower_bound.mainPart(), carl::sample(delta_range, true));
    } // else : r - a*delta <= x <= r + b*delta (a,b > 0) => can use r
    return DeltaRational(lower_bound.mainPart(), Rational(0));
    
}

class Level {

    private:
        std::size_t m_level;        /// the actual level
        FMPlexTableau m_tableau;    ///

        std::vector<std::size_t> m_backtrack_levels;    ///
        std::set<RowIndex> m_ignore_for_eliminators;    ///

        std::map<ColumnIndex,Column>::const_iterator m_eliminated_column;   ///
        EliminationType m_elimination_type;                                 ///
        bool m_elimination_chosen;

        std::vector<std::size_t> m_tried_rows;      /// Indicates which of the tableau's rows have been tried as eliminators.
        std::vector<Eliminator> m_open_eliminators; /// Indicates which of the tableau's rows can still be tried as eliminators.

        std::set<std::size_t> m_unsat_core; /// The **original** rows that make the so far visited children UNSAT.
        bool m_finished = false;            /// Flag indicating whether all children were constructed.
    
    public:
        // Constructors
        Level(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index)
        : m_level(0),
          m_tableau(constraints, variable_index),
          m_backtrack_levels(constraints.size(), 0),
          m_ignore_for_eliminators(),
          m_elimination_chosen(false) {} // todo: duplicates/redundancies?

        Level(std::size_t n_constraints, std::size_t level, ColumnIndex rhs_index)
        : m_level(level),
          m_tableau(n_constraints, rhs_index),
          m_backtrack_levels(n_constraints, 0),
          m_ignore_for_eliminators(),
          m_elimination_chosen(false) {}

        Level(const FMPlexTableau& tableau)
        : m_level(0),
          m_tableau(tableau),
          m_backtrack_levels(tableau.nr_of_rows(), 0),
          m_ignore_for_eliminators(),
          m_elimination_chosen(false) {} // REVIEW: dont want to copy

        // todo: destructor?

        template<bool IgnoreUsed, VariableHeuristic VH>
        bool choose_elimination_column() {
            m_elimination_chosen = true;
            if constexpr (VH == VariableHeuristic::COLUMN_ORDER) {
                SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "using column order");
                return choose_elimination_column_column_order<IgnoreUsed>();
            }   
            if constexpr (VH == VariableHeuristic::LEAST_BRANCHES) {
                SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "using least branches");
                return choose_elimination_column_least_branches<IgnoreUsed>();
            }
            assert(false); // unreachable
            return false;
        }

        template<bool USE_BT, bool IGNORE_USED>
        Level next_child() {
            SMTRAT_LOG_DEBUG("smtrat.fmplex", "constructing next child of level " << m_level);

            if (m_elimination_type == EliminationType::NONE) {
                m_finished = true;
                Level child = eliminate_without_bounds<USE_BT,IGNORE_USED>();
                SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "->\n" << child);
                return child;
            } else { // todo: eliminator choice heuristic
                SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "number of eliminators left: " << m_open_eliminators.size());

                Eliminator e = m_open_eliminators.back();
                m_open_eliminators.pop_back();
                if (m_open_eliminators.empty()) m_finished = true;

                m_tried_rows.push_back(e.row);
                if constexpr (IGNORE_USED) {
                    m_ignore_for_eliminators.emplace(e.row);
                }
                
                Level child = eliminate<USE_BT,IGNORE_USED>(e);
                SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "->" << child);
                return child;
            }
        }

        void assign_implicitly_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const {
            // set implicitly eliminated variables to zero
            std::vector<ColumnIndex> non_zero_variable_columns = m_tableau.non_zero_variable_columns();
            for (const auto col : non_zero_variable_columns) {
                if (col == m_eliminated_column->first) continue;
                if (m.count(col) == 0) m.emplace(col, DeltaRational(0)); // REVIEW: better with lower_bound?
            }
        }

        void assign_single_bounded(std::map<std::size_t, DeltaRational>& m) const {
            auto col_it = m_eliminated_column->second.begin();
            std::optional<DeltaRational> strictest_bound;
            if (m_tableau.value_at(*col_it) > 0) {
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    DeltaRational current_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!strictest_bound || (current_bound < (*strictest_bound))) {
                        strictest_bound = current_bound;
                    }
                }
                m.emplace(m_eliminated_column->first, choose_value_below(*strictest_bound));
            } else {
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    DeltaRational current_bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!strictest_bound || (current_bound > (*strictest_bound))) {
                        strictest_bound = current_bound;
                    }
                }
                m.emplace(m_eliminated_column->first, choose_value_above(*strictest_bound));
            }
        }

        void assign_double_bounded(std::map<std::size_t, DeltaRational>& m) const {
            auto col_it = m_eliminated_column->second.begin();
            std::optional<DeltaRational> lower_bound, upper_bound;
            if (m_elimination_type == EliminationType::LBS) {
                lower_bound = m_tableau.bound_value(m_tried_rows.back(), m_eliminated_column->first, m);
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    if (m_tableau.value_at(*col_it) < 0) continue;

                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!upper_bound || (bound < (*upper_bound))) {
                        upper_bound = bound;
                    }
                }
            } else {
                upper_bound = m_tableau.bound_value(m_tried_rows.back(), m_eliminated_column->first, m);
                for (; col_it != m_eliminated_column->second.end(); col_it++) {
                    if (m_tableau.value_at(*col_it) > 0) continue;

                    DeltaRational bound = m_tableau.bound_value(col_it->row, m_eliminated_column->first, m);
                    if (!lower_bound || (bound > (*lower_bound))) {
                        lower_bound = bound;
                    }
                }
            }

            assert(lower_bound.has_value() && upper_bound.has_value());
            m.emplace(m_eliminated_column->first, choose_value_between(*lower_bound, *upper_bound));
        }

        void assign_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const {
            SMTRAT_LOG_DEBUG("smtrat.fmplex", "Assigning " << m_eliminated_column->first);

            // todo: can use heuristics and optimize if only weak bounds are present

            assign_implicitly_eliminated_variables(m);

            switch (m_elimination_type) {
                case EliminationType::NONE:
                    assign_single_bounded(m);
                    break;
                case EliminationType::LBS:
                case EliminationType::UBS:
                    assign_double_bounded(m);
                    break;
                default: // unreachable
                    assert(false);
            }
            SMTRAT_LOG_DEBUG("smtrat.fmplex", "-> value for " << m_eliminated_column->first << ": " << m.at(m_eliminated_column->first));
        }

        std::optional<Conflict> earliest_conflict(const std::set<std::size_t>& equality_origins) const {
            std::optional<Conflict> result;
            for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
                if (!m_tableau.is_row_conflict(i)) continue;
                
                Origins ogs = m_tableau.origins(i);
                bool non_neg = true;
                for (const auto o : ogs.with_negative_coeff) {
                    if (equality_origins.count(o) == 0) {
                        non_neg = false;
                        break;
                    }
                }
                if (non_neg) {
                    return Conflict{true, 0, ogs.all_indices};
                }
                if (!result || (m_backtrack_levels[i] < result->level)) {
                    result = Conflict{false, m_backtrack_levels[i], ogs.all_indices};
                }
            }
            return result;
        }

        void add_to_unsat_core(const std::set<std::size_t>& child_unsat_core) {
            m_unsat_core.insert(child_unsat_core.begin(), child_unsat_core.end());
        }

        inline std::set<std::size_t> unsat_core() const { return m_unsat_core; }

        inline bool finished() const { return m_finished; }

        inline bool is_lhs_zero() const { return m_tableau.is_lhs_zero(); }

        inline bool has_elimination_column() const {return m_elimination_chosen; }

        inline ColumnIndex eliminated_column_index() const { return m_eliminated_column->first; }

    private:

        template<bool IgnoreUsed>
        void collect_eliminators() {
            bool collect_lbs = (m_elimination_type == EliminationType::LBS);
            for (const auto& col_elem : m_eliminated_column->second) {
                if constexpr (IgnoreUsed) {
                    if (m_ignore_for_eliminators.count(col_elem.row) == 1) {
                        SMTRAT_STATISTICS_CALL(if ((val < 0) == collect_lbs) NewFMPlexStatistics::get_instance().ignored_branches(1));
                        continue;
                    }
                }
                Rational val = m_tableau.value_at(col_elem);
                if ((val < 0) == collect_lbs) {
                    m_open_eliminators.emplace_back(col_elem.row, val);
                }
            }
            SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "collected eliminators: " << [](auto es){
                std::string res = "";
                for (const auto& e : es) res += std::to_string(e.row) + ", ";
                return res;
            }(m_open_eliminators));
            SMTRAT_STATISTICS_CALL(NewFMPlexStatistics::get_instance().branches(m_open_eliminators.size()));
        }

        struct Bounds {
            std::size_t lbs;
            std::size_t ignored_lbs;
            std::size_t ubs;
            std::size_t ignored_ubs;
        };

        template<bool IgnoreUsed>
        Bounds count_bounds(const Column& column) {
            Bounds result = {0, 0, 0, 0};
            for (const auto& e : column) {
                if (m_tableau.value_at(e) > 0) {
                    result.ubs++;
                    if constexpr (IgnoreUsed) {
                        if (m_ignore_for_eliminators.count(e.row) == 1) result.ignored_ubs++;
                    }
                } else {
                    result.lbs++;
                    if constexpr (IgnoreUsed) {
                        if (m_ignore_for_eliminators.count(e.row) == 1) result.ignored_lbs++;
                    }
                }
            }
            return result;
        }

        template<bool IgnoreUsed>
        bool choose_elimination_column_column_order() {
            auto col_it = m_tableau.columns_begin();
            if (col_it->first >= m_tableau.rhs_index()) return false;

            m_eliminated_column = col_it;
            SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "chose column" << m_eliminated_column->first);

            Bounds bounds = count_bounds<IgnoreUsed>(col_it->second());

            if ((bounds.lbs == 0) || (bounds.ubs == 0)) {
                m_elimination_type = EliminationType::NONE;
                return true;
            }

            if constexpr (IgnoreUsed) {
                if ((bounds.ignored_lbs == bounds.lbs) || (bounds.ignored_ubs == bounds.ubs)) {
                    return false;
                }
                bounds.lbs -= bounds.ignored_lbs;
                bounds.ubs -= bounds.ignored_ubs;
            }
            
            m_elimination_type = (bounds.lbs < bounds.ubs) ? EliminationType::LBS : EliminationType::UBS;

            collect_eliminators<IgnoreUsed>();
            return true;
        }

        // REVIEW: fix encapsulation!
        template<bool IgnoreUsed>
        bool choose_elimination_column_least_branches() {
            std::optional<size_t> fewest_branches;

            for (auto col_it = m_tableau.columns_begin(); col_it != m_tableau.columns_end(); col_it++) {
                // We only consider the columns corresponding to the original variables
                if (col_it->first >= m_tableau.rhs_index()) break;

                Bounds bounds = count_bounds<IgnoreUsed>(col_it->second);

                if (bounds.lbs == 0 || bounds.ubs == 0) {
                    m_eliminated_column = col_it;
                    m_elimination_type = EliminationType::NONE;
                    return true;
                }

                if constexpr (IgnoreUsed) {
                    if ((bounds.ignored_lbs == bounds.lbs) || (bounds.ignored_ubs == bounds.ubs)) {
                        return false;
                    }
                    bounds.lbs -= bounds.ignored_lbs;
                    bounds.ubs -= bounds.ignored_ubs;
                }

                std::size_t min = std::min(bounds.lbs, bounds.ubs);
                if (!fewest_branches || (min < (*fewest_branches))) {
                    fewest_branches = min;
                    m_eliminated_column = col_it;
                    m_elimination_type = (bounds.lbs < bounds.ubs) ? EliminationType::LBS : EliminationType::UBS;
                }
            }
            assert(fewest_branches.has_value());
            SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "collecting eliminators");
            collect_eliminators<IgnoreUsed>();
            return true;
        }

        template<bool USE_BT, bool IGNORE_USED> 
        Level eliminate(const Eliminator& e) const {
            SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "eliminating column " << m_eliminated_column->first << " with row " << e.row);

            Level result(m_tableau.nr_of_rows() - 1, m_level + 1, m_tableau.rhs_index());

            Column::const_iterator col_it = m_eliminated_column->second.begin();

            auto process_row = [&](const RowIndex i, const RowIndex output_row) {
                if ((col_it != m_eliminated_column->second.end()) && (i == col_it->row)) {
                    SMTRAT_STATISTICS_CALL(NewFMPlexStatistics::get_instance().generated_constraints(1));
                    Row row = m_tableau.combine(e.row, i, m_eliminated_column->first, e.coeff, m_tableau.value_at(*col_it));
                    result.m_tableau.append_row(row);
                    if constexpr (USE_BT) {
                        if ((e.coeff > 0) == (m_tableau.value_at(*col_it) > 0)) result.m_backtrack_levels[output_row] = m_level + 1;
                        else result.m_backtrack_levels[output_row] = std::max(m_backtrack_levels[e.row], m_backtrack_levels[i]);
                    }
                    col_it++;
                } else {
                    result.m_tableau.copy_row_from(i, m_tableau);
                    if constexpr (USE_BT) result.m_backtrack_levels[output_row] = m_backtrack_levels[i];
                }
                if constexpr (IGNORE_USED) {
                    if (m_ignore_for_eliminators.count(i) == 1) {
                        result.m_ignore_for_eliminators.emplace_hint(result.m_ignore_for_eliminators.end(), output_row);
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

            return result;
        }

        template<bool UseBT, bool IgnoreUsed> 
        Level eliminate_without_bounds() const {
            SMTRAT_LOG_DEBUG("smtrat.fmplex.level", "eliminating column " << m_eliminated_column->first << " without row");

            Level result(m_tableau.nr_of_rows() - m_eliminated_column->second.size(), m_level + 1, m_tableau.rhs_index());
            RowIndex added_row = 0;
            Column::const_iterator col_it = m_eliminated_column->second.begin();

            for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
                if ((col_it != m_eliminated_column->second.end()) && (i == col_it->row)) { // Requires the column elements to be in ascending order!!
                    col_it++;
                    continue;
                } 

                result.m_tableau.copy_row_from(i, m_tableau);
                if constexpr (UseBT) {
                    result.m_backtrack_levels[added_row] = m_backtrack_levels[i];
                }
                if constexpr (IgnoreUsed) {
                    if (m_ignore_for_eliminators.count(i) == 1) {
                        result.m_ignore_for_eliminators.emplace_hint(result.m_ignore_for_eliminators.end(), added_row);
                    }
                }
                added_row++;
            }

            return result;
        }

        friend std::ostream& operator<<(std::ostream& os, const Level& level);
};

inline std::ostream& operator<<(std::ostream& os, const Level& level) {
    os << "Level " << level.m_level << ":\n";
    os << "BT info (row : BT-level) : [";
    for (std::size_t i = 0; i < level.m_backtrack_levels.size(); i++) {
        os << "(" << i << " : " << level.m_backtrack_levels[i] << ")";
    }
    os << "]\n";
    os << "ignored rows: {";
    for (auto i : level.m_ignore_for_eliminators) {
        os << i << ", ";
    }
    os << "}\n";
    os << level.m_tableau;
    return os;
}

} // namespace smtrat::fmplex