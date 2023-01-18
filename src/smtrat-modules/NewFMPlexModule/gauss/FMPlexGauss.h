namespace smtrat::fmplex {

class FMPlexGauss : Gauss {
    struct Pivot {
        RowIndex row;
        ColumnIndex col;
        Rational coeff;
        Pivot(RowIndex _row, ColumnIndex _col, Rational _coeff) : row(_row), col(_col), coeff(_coeff) {}
    };

    private:    

    std::vector<Row> m_rows;
    std::map<ColumnIndex, Column> m_columns;

    ColumnIndex m_rhs_index;
    ColumnIndex m_delta_index;
    ColumnIndex m_first_origin_index;
    std::set<RowIndex> m_equalities;
    std::set<RowIndex> m_disequalities;
    std::set<RowIndex> m_inequalities;
    std::vector<Pivot> m_pivot_order;

    const Rational& value_at(const ColumnElement& ce) {
        return m_rows[ce.row][ce.position_in_row].value;
    }

    void recompute_columns() {
        for (auto& [index, column] : m_columns) column.clear();
        for (std::size_t r = 0; r < m_rows.size(); r++) {
            for (std::size_t i = 0; i < m_rows[r].elements.size(); i++) {
                m_columns[m_rows[r][i].column].emplace_back(r,i);
            }
        }
    }

    void apply_gauss_step(Pivot pivot, const std::set<RowIndex>& inactive_equalities) { // TODO: columns are incorrect after this
        Column col = m_columns.at(pivot.col);
        for (const ColumnElement& ce : col) {
            if (inactive_equalities.count(ce.row) == 1) continue;
            Row result;
            result.elements.reserve(m_columns.size()-1); // REVIEW: or minimum with pivot.size+other.size?
            Rational pivot_scale;
            Rational other_scale;
            result.relation = m_rows[ce.row].relation;
            // REVIEW: skalierung anpassen? Nur mit Integers arbeiten?
            if (value_at(ce) > 0/*pivot_coeff > 0*/) {
                pivot_scale = -1/pivot.coeff; //-other_coeff;
                other_scale = 1/value_at(ce); //pivot_coeff;
            } else { // pivot_coeff < 0
                pivot_scale = 1/pivot.coeff;//other_coeff;
                other_scale = -1/value_at(ce);//-pivot_coeff;
            }

            Row::ConstIterator pivot_iter = m_rows[pivot.row].begin();
            Row::ConstIterator other_iter = m_rows[ce.row].begin();
            Row::ConstIterator pivot_end = m_rows[pivot.row].end();
            Row::ConstIterator other_end = m_rows[ce.row].end();
            while((pivot_iter != pivot_end) && (other_iter != other_end)) {
                if (pivot_iter->column < other_iter->column) {
                    result.elements.emplace_back(pivot_iter->column, pivot_scale*(pivot_iter->value));
                    pivot_iter++;
                } else if (pivot_iter->column > other_iter->column) {
                    result.elements.emplace_back(other_iter->column, other_scale*(other_iter->value));
                    other_iter++;
                } else { // same column
                    if (pivot_iter->column != pivot.col) { // we know that the eliminated colum will be zero
                        Rational value = other_scale*(other_iter->value) + pivot_scale*(pivot_iter->value);
                        if (!carl::is_zero(value)) result.elements.emplace_back(pivot_iter->column, value);
                    }
                    pivot_iter++;
                    other_iter++;
                }
            }
            for( ; pivot_iter != pivot_end; pivot_iter++) {
                result.elements.emplace_back(pivot_iter->column, pivot_scale*(pivot_iter->value));
            }
            for( ; other_iter != other_end; other_iter++) {
                result.elements.emplace_back(other_iter->column, other_scale*(other_iter->value));
            }
            m_rows[ce.row] = result; // REVIEW: is there a better in-place assignment?
        }
        recompute_columns();
    }

    std::optional<Pivot> choose_gaussian_pivot(const std::set<RowIndex>& inactive_rows) {
        // TODO: use heuristics
        for (const RowIndex r : m_equalities) {
            if (inactive_rows.count(r) == 1) continue;
            ColumnIndex c = m_rows[r].elements[0].column;
            if (c < m_rhs_index) return Pivot(r,c,m_rows[r].elements[0].value);
        }
        return std::nullopt;
    }

    void append_row(const Row& row) {
        for (ColumnPosition i = 0; i < row.elements.size(); i++) {
            RowElement r = row.elements[i];
            auto it = m_columns.lower_bound(r.column);
            if ((it == m_columns.end()) || (it->first != r.column)) {
                it = m_columns.insert(it, {r.column, std::vector<ColumnElement>()});
            }
            it->second.emplace_back(m_rows.size(), i);
        }
        m_rows.push_back(row);
    }

    std::set<std::size_t> origins (const RowIndex i) {
        std::set<std::size_t> result;
        for (auto it = m_rows[i].elements.end(); it != m_rows[i].elements.begin();) {
            it--;
            if (it->column < m_first_origin_index) break;
            result.emplace_hint(result.begin(), it->column - m_first_origin_index);
        }
        return result;
    }

    DeltaRational bound_value(const RowIndex ri, const ColumnIndex ci_eliminated, const std::map<ColumnIndex, DeltaRational>& model) const {
        DeltaRational bound(0);
        Rational coeff;
        for (const auto& row_elem : m_rows[ri]) {
            // we are only interested in the lhs and rhs, not the origins
            if (row_elem.column > m_delta_index) break;
            else if (row_elem.column == m_rhs_index) bound += row_elem.value;
            else if (row_elem.column == m_delta_index) bound += DeltaRational(0, row_elem.value);
            else if (row_elem.column == ci_eliminated) coeff = row_elem.value;
            else {
                auto it = model.find(row_elem.column);
                if (it != model.end()) bound -= ((it->second) * row_elem.value);
            }
        }
        SMTRAT_LOG_DEBUG("smtrat.fmplex", "Bound for var " << ci_eliminated << " from row " << ri << ": " << m_rows[ri] << " is " << bound << "/" << coeff);
        return bound / coeff;
    }

    public:
    void init(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) override {
        // TODO: reset function?
        m_rows = std::vector<Row>();
        m_columns.clear();
        m_disequalities.clear();
        m_equalities.clear();
        m_inequalities.clear();
        m_pivot_order.clear();
        SMTRAT_LOG_DEBUG("smtrat.gauss", "initializing gauss with constraints " << constraints << " and variable index " << variable_index);
        m_rows.reserve(constraints.size());
        m_rhs_index = variable_index.size();
        m_delta_index = m_rhs_index + 1;
        m_first_origin_index = m_delta_index + 1;

        bool remove_strict = false;
        for (RowIndex row = 0; row < constraints.size(); row++) {
            Row current_row;
            const FormulaT& c = constraints[row];

            carl::Relation r = c.constraint().relation();
            remove_strict = (r == carl::Relation::LESS) || (r == carl::Relation::GREATER);
            bool is_inequality = (remove_strict || (r == carl::Relation::LEQ) || (r == carl::Relation::GEQ));
            current_row.relation = is_inequality ? carl::Relation::LEQ : r;
            if (is_inequality) m_inequalities.emplace_hint(m_inequalities.end(), row);
            else if (r == carl::Relation::EQ) m_equalities.emplace_hint(m_equalities.end(), row);
            else if (r == carl::Relation::NEQ) m_disequalities.emplace_hint(m_disequalities.end(), row);

            Poly p = c.constraint().lhs();
            current_row.elements.reserve(p.nr_terms() + 1);
            Rational turning_factor(1);
            if ((r == carl::Relation::GEQ) || (r == carl::Relation::GREATER)) turning_factor = -1;
            for (const auto& term : p) {
                if (term.is_constant()) continue; // REVIEW: remove this line and filter out constant part before
                ColumnIndex column = variable_index.at(term.single_variable());
                current_row.elements.emplace_back(column, turning_factor * term.coeff());
            }
            std::sort(current_row.elements.begin(), current_row.elements.end(),
                [](const auto& lhs, const auto& rhs){ return lhs.column < rhs.column; }
            );
            if (p.has_constant_term()) current_row.elements.emplace_back(m_rhs_index, (-turning_factor) * p.constant_part());
            if (remove_strict) current_row.elements.emplace_back(m_delta_index, Rational(-1));
            current_row.elements.emplace_back(m_first_origin_index + row, Rational(1));
            append_row(current_row);
        }
        SMTRAT_LOG_DEBUG("smtrat.gauss", "result: " << m_rows.size() << " rows and " << m_columns.size() << " columns");
    }

    void apply_gaussian_elimination() override {
        std::set<RowIndex> used_equalities;
        std::optional<Pivot> pivot = choose_gaussian_pivot(used_equalities);
        while (pivot) {
            SMTRAT_LOG_DEBUG("smtrat.gauss", "chosen pivot: row " << pivot->row << ", col " << pivot->col);
            used_equalities.emplace(pivot->row);
            m_pivot_order.push_back(*pivot);
            apply_gauss_step(*pivot, used_equalities);
            pivot = choose_gaussian_pivot(used_equalities);
        }
    }

    FMPlexTableau get_transformed_inequalities() override {
        FMPlexTableau result(m_inequalities.size(), m_rhs_index);
        for (RowIndex i : m_inequalities) {
            result.append_row(m_rows[i]);
        }
        return result;
    }

    std::optional<Conflict> find_conflict() override {
        for (RowIndex i = 0; i < m_rows.size(); i++) {
            if (m_rows[i][0].column < m_rhs_index) continue;
            if (m_rows[i][0].column <= m_delta_index) {
                if (m_rows[i].relation == carl::Relation::EQ) return Conflict {true, 0, origins(i)};
                if (m_rows[i].relation == carl::Relation::NEQ) continue;
                if (m_rows[i][0].value < 0) return Conflict {true, 0, origins(i)};
            }
            if (carl::is_strict(m_rows[i].relation)) return Conflict {true, 0, origins(i)};
        }
        return std::nullopt;
    }

    std::vector<Conflict> find_all_conflicts() {
        std::vector<Conflict> result;
        for (RowIndex i = 0; i < m_rows.size(); i++) {
            if (m_rows[i][0].column < m_rhs_index) continue;
            if (m_rows[i][0].column <= m_delta_index) {
                if (m_rows[i].relation == carl::Relation::EQ) {
                    result.push_back(Conflict {true, 0, origins(i)});
                    continue;
                }
                if (m_rows[i].relation == carl::Relation::NEQ) continue;
                if (m_rows[i][0].value < 0) {
                    result.push_back(Conflict {true, 0, origins(i)});
                    continue;
                }
            }
            if (carl::is_strict(m_rows[i].relation)) result.push_back(Conflict {true, 0, origins(i)});
        }
        return result;
    }

    void assign_variables(std::map<std::size_t, DeltaRational>& working_model) override {
        for (std::size_t i = m_pivot_order.size(); i > 0; i--) {
            fmplex::DeltaRational v = bound_value(m_pivot_order[i-1].row, m_pivot_order[i-1].col, working_model);
            working_model.emplace(m_pivot_order[i-1].col, v);
            SMTRAT_LOG_DEBUG("smtrat.gauss", "assigning " << v << " to " << m_pivot_order[i-1].col);
        }
        for (const auto& [idx, _col] : m_columns) {
            if (idx >= m_rhs_index) break;
            if (working_model.count(idx) == 0) working_model.emplace(idx, 0);
        }
    }
};

} // namespace smtrat::fmplex