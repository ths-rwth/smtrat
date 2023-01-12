#pragma once
#include "../NewFMPlexModule/Tableau.h"

namespace smtrat::foumo {

using Conflict = std::set<std::size_t>;
using DeltaRational = smtrat::fmplex::DeltaRational;
using ColumnIndex = smtrat::fmplex::ColumnIndex;
using RowIndex = smtrat::fmplex::RowIndex;
using Column = smtrat::fmplex::Column;
using Row = smtrat::fmplex::Row;
using FMPlexTableau = smtrat::fmplex::FMPlexTableau;
using ModelHeuristic = smtrat::fmplex::ModelHeuristic;


class Level {

    private:
        std::size_t m_level;        /// the actual level
        smtrat::fmplex::FMPlexTableau m_tableau;    ///

        std::map<ColumnIndex,Column>::const_iterator m_eliminated_column;   ///

        Column m_ubs;
        Column m_lbs; 
    
    public:
        // Constructors
        Level(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index)
        : m_level(0),
          m_tableau(constraints, variable_index) {} // todo: duplicates/redundancies?

        Level(std::size_t n_constraints, std::size_t level, ColumnIndex rhs_index)
        : m_level(level),
          m_tableau(n_constraints, rhs_index) {}

        Level(const FMPlexTableau& tableau)
        : m_level(0),
          m_tableau(tableau) {} // REVIEW: dont want to copy

        // todo: destructor?

        void choose_elimination_column() {
            std::optional<size_t> fewest_new_constraints;

            for (auto col_it = m_tableau.columns_begin(); col_it != m_tableau.columns_end(); col_it++) {
                // We only consider the columns corresponding to the original variables
                if (col_it->first >= m_tableau.rhs_index()) break;

                Column cur_lbs, cur_ubs;
                
                for (const auto& e : col_it->second) {
                    if (m_tableau.value_at(e) > 0) {
                        cur_ubs.push_back(e);
                    } else {
                        cur_lbs.push_back(e);
                    }
                }

                std::size_t cur_new_constraints = cur_lbs.size()*cur_ubs.size();
                if (cur_new_constraints == 0) {
                    m_eliminated_column = col_it;
                    m_lbs = cur_lbs;
                    m_ubs = cur_ubs;
                    return;
                }

                if (!fewest_new_constraints || (cur_new_constraints < (*fewest_new_constraints))) {
                    fewest_new_constraints = cur_new_constraints;
                    m_eliminated_column = col_it;
                    m_lbs = cur_lbs;
                    m_ubs = cur_ubs;
                }
            }
            assert(fewest_new_constraints.has_value());
        }

        Level eliminate() {
            SMTRAT_LOG_DEBUG("smtrat.foumo.level", "eliminating column " << m_eliminated_column->first);

            Level result(m_tableau.nr_of_rows() - m_lbs.size() - m_ubs.size() + (m_lbs.size()*m_ubs.size()), m_level + 1, m_tableau.rhs_index());

            for (const auto& lb : m_lbs) {
                for (const auto& ub : m_ubs) {
                    Row row = m_tableau.combine(lb.row, ub.row, m_eliminated_column->first, m_tableau.value_at(lb), m_tableau.value_at(ub));
                    // TODO: Imbert
                    result.m_tableau.append_row(row);
                }
            }

            Column::const_iterator col_it = m_eliminated_column->second.begin();
            for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {// Requires the column index elements to be in ascending order!!
                if ((col_it != m_eliminated_column->second.end()) && (col_it->row == i)) col_it++;
                else result.m_tableau.copy_row_from(i, m_tableau);
            }

            return result;
        }

        void assign_implicitly_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const {
            // set implicitly eliminated variables to zero
            std::vector<ColumnIndex> non_zero_variable_columns = m_tableau.non_zero_variable_columns();
            for (const auto col : non_zero_variable_columns) {
                if (col == m_eliminated_column->first) continue;
                if (m.count(col) == 0) m.emplace(col, DeltaRational(0)); // REVIEW: better with lower_bound?
            }
        }

        template<ModelHeuristic MH>
        void assign_eliminated_variables(std::map<std::size_t, DeltaRational>& m) const {
            SMTRAT_LOG_DEBUG("smtrat.foumo", "Assigning " << m_eliminated_column->first);

            // todo: can use heuristics and optimize if only weak bounds are present

            assign_implicitly_eliminated_variables(m);

            std::optional<DeltaRational> strictest_lb, strictest_ub;
            for (const auto& lb : m_lbs) {
                DeltaRational v = m_tableau.bound_value(lb.row, m_eliminated_column->first, m);
                if (!strictest_lb || (v > (*strictest_lb))) {
                    strictest_lb = v;
                }
            }
            for (const auto& ub : m_ubs) {
                DeltaRational v = m_tableau.bound_value(ub.row, m_eliminated_column->first, m);
                if (!strictest_ub || (v < (*strictest_ub))) {
                    strictest_ub = v;
                }
            }

            if constexpr (MH == ModelHeuristic::ON_BOUND) {
                if (!strictest_lb) {
                    m.emplace(m_eliminated_column->first, *strictest_ub);
                } else {
                    m.emplace(m_eliminated_column->first, *strictest_lb);
                }
            }
            if constexpr (MH == ModelHeuristic::SAMPLE_MID) {
                if (!strictest_lb) {
                    m.emplace(m_eliminated_column->first, smtrat::fmplex::choose_value_below(*strictest_ub));
                } else if (!strictest_ub) {
                    m.emplace(m_eliminated_column->first, smtrat::fmplex::choose_value_above(*strictest_lb));
                } else {
                    m.emplace(m_eliminated_column->first, smtrat::fmplex::choose_value_between(*strictest_lb, *strictest_ub));
                }
            }
            SMTRAT_LOG_DEBUG("smtrat.foumo", "-> value for " << m_eliminated_column->first << ": " << m.at(m_eliminated_column->first));
        }

        std::optional<Conflict> smallest_conflict() const {
            std::optional<Conflict> result;
            for (RowIndex i = 0; i < m_tableau.nr_of_rows(); i++) {
                if (!m_tableau.is_row_conflict(i)) continue;
                
                smtrat::fmplex::Origins ogs = m_tableau.origins(i);
                if (!result || (ogs.all_indices.size() < result->size())) {
                    result = ogs.all_indices;
                }
            }
            return result;
        }

        inline bool is_lhs_zero() const { return m_tableau.is_lhs_zero(); }

        inline ColumnIndex eliminated_column_index() const { return m_eliminated_column->first; }
};

} // namespace smtrat::fmplex