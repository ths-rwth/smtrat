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
        };

        struct ColumnElement {
            RowIndex row;
            ColumnPosition position_in_row;
            ColumnElement(const RowIndex r, const ColumnPosition p) : row(r), position_in_row(p) {}
        };

        using Column = std::vector<ColumnElement>;

        class FMPlexTableau { // REVIEW: memory management : alle RowElements in einen grossen vector?
            /*
            Tableau before applying Gauss looks as follows:
                       | x_1 ... x_n | b | eq_1 ... eq_k | ineq_1 ... ineq_m |
                       |-------------|---|---------------|-------------------|
                  eq_1 |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
                   ... |  .  ...  .  | . |  .   ...  .   |   .    ...   .    |
                  eq_k |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
                       |-------------|---|---------------|-------------------|
                ineq_1 |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
                  ...  |  .  ...  .  | . |  .   ...  .   |   .    ...   .    |
                ineq_m |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
    
            After Gauss, the **rows** corresponding to equalities are eliminated, but the columns are retained.
                       | x_1 ... x_n | b | eq_1 ... eq_k | ineq_1 ... ineq_m |
                       |-------------|---|---------------|-------------------|
                       |-------------|---|---------------|-------------------|
                ineq_1 |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
                  ...  |  .  ...  .  | . |  .   ...  .   |   .    ...   .    |
                ineq_m |  *  ...  *  | * |  *   ...  *   |   *    ...   *    |
            */

            private:
                /// vector containing the rows
                std::vector<Row> m_rows;
                /// number of rows
                std::size_t m_nr_rows;
                /// map containing the non-zero columns
                std::map<ColumnIndex,Column> m_columns;

                ColumnIndex m_rhs_index;

                // REVIEW: is storing this information better than computation on the fly?
                std::vector<RowIndex> m_equalities;
                std::vector<RowIndex> m_disequalities;
                std::vector<RowIndex> m_inequalities;

            public:
                FMPlexTableau(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) { // todo: duplicates/redundancies?
                    m_rows.reserve(constraints.size());
                    m_nr_rows = constraints.size();
                    m_rhs_index = variable_index.size();

                    for (RowIndex row = 0; row < constraints.size(); row++) {
                        Row current_row;
                        const FormulaT& c = constraints[row];
                        carl::Relation r = c.constraint().relation();
                        Poly p = c.constraint().lhs();
                        current_row.elements.reserve(p.nr_terms()+1);

                        if (r == carl::Relation::GEQ || r == carl::Relation::GREATER) {
                            current_row.relation = (carl::is_weak(r) ? carl::Relation::LEQ : carl::Relation::LESS);
                            for (const auto& term : p) {
                                if (term.is_constant()) continue;
                                ColumnIndex column = variable_index.at(term.single_variable());
                                current_row.elements.emplace_back(column, -term.coeff());
                            }
                        } else {
                            current_row.relation = r;
                            for (const auto& term : p) {
                                // REVIEW: we know where the constant term will be after sorting
                                if (term.is_constant()) continue;
                                ColumnIndex column = variable_index.at(term.single_variable());
                                current_row.elements.emplace_back(column, term.coeff());
                            }
                        }
                        std::sort(current_row.elements.begin(), current_row.elements.end(),
			                [](const auto& lhs, const auto& rhs){ return lhs.column < rhs.column; }
		                );
                        if (p.has_constant_term()) current_row.elements.emplace_back(m_rhs_index, -p.constant_part());
                        current_row.elements.emplace_back(m_rhs_index + row + 1, Rational(1));
                        append_row(current_row);
                    }
                }

                FMPlexTableau(std::size_t n_rows, ColumnIndex rhs_index) {
                    m_rows.reserve(n_rows);
                    m_rhs_index = rhs_index;
                    m_nr_rows = n_rows;
                }

                std::size_t nr_of_rows() const {
                    return m_nr_rows;
                }

                std::vector<RowIndex> disequality_rows() const { // REVIEW: reference?
                    return m_disequalities;
                }

                ColumnIndex rhs_index() const {
                    return m_rhs_index;
                }

                Rational value_at(const ColumnElement& ce) const {
                    return m_rows[ce.row].elements[ce.position_in_row].value;
                }

                carl::Relation relation(const RowIndex row) const {
                    return m_rows[row].relation;
                }

                std::size_t origin(ColumnIndex ci) const {
                    assert(ci > m_rhs_index);
                    return ci - m_rhs_index - 1;
                }

                std::map<ColumnIndex, Column>::const_iterator columns_begin() {
                    return m_columns.begin();
                }

                std::map<ColumnIndex, Column>::const_iterator columns_end() {
                    return m_columns.end();
                }

                std::pair<std::set<std::size_t>, bool> origins(RowIndex ri) const {
                    std::set<std::size_t> result;
                    bool non_neg = true;
                    std::vector<RowElement>::const_iterator row_it = m_rows[ri].elements.end();
                    while (row_it != m_rows[ri].elements.begin()) {
                        row_it--;
                        if (row_it->column <= m_rhs_index) break;
                        result.emplace_hint(result.begin(), origin(row_it->column));
                        if (row_it->value < 0) non_neg = false;
                    }
                    return std::make_pair(result, non_neg);
                }

                std::pair<bool, bool> is_row_conflict(const RowIndex row) const {
                    auto row_it = m_rows[row].elements.begin();
                    bool test_strict = false;
                    if (row_it->column < m_rhs_index) {
                        return std::make_pair(false,false);
                    } else if (row_it->column == m_rhs_index) {
                        if ((m_rows[row].relation != carl::Relation::EQ) && (row_it->value > 0))
                            return std::make_pair(false,false);
                    } else if (m_rows[row].relation == carl::Relation::LEQ) {
                        return std::make_pair(false,false);
                    } else if (m_rows[row].relation == carl::Relation::LESS) {
                        test_strict = true;
                    }
                    return std::make_pair(true, test_strict);
                }

                void append_row(const Row& row) {
                    for (ColumnPosition i = 0; i < row.elements.size(); i++) {
                        RowElement r = row.elements[i];
                        // REVIEW: the same could be achieved by calling m_columns.insert({r.column, std::vector<ColumnElement>()}); without lower_bound
                        auto it = m_columns.lower_bound(r.column);
                        if ((it == m_columns.end()) || (it->first != r.column)) {
                            it = m_columns.insert(it, {r.column, std::vector<ColumnElement>()});
                        }
                        it->second.emplace_back(m_rows.size(), i);
                    }
                    if (row.relation == carl::Relation::EQ) m_equalities.push_back(m_rows.size());
                    else if (row.relation == carl::Relation::NEQ) m_disequalities.push_back(m_rows.size());
                    else {
                        assert((row.relation == carl::Relation::LEQ) || (row.relation == carl::Relation::LESS) 
                        || (row.relation == carl::Relation::GEQ) || (row.relation == carl::Relation::GREATER));
                        m_inequalities.push_back(m_rows.size());
                    }
                    m_rows.push_back(row);
                }

                void copy_row_from(const RowIndex row, const FMPlexTableau& other) {
                    append_row(other.m_rows[row]);
                }

                std::pair<Row, bool> combine(const RowIndex pivot_row, const RowIndex other_row,
                 const ColumnIndex eliminated_col, const Rational& pivot_coeff, const Rational& other_coeff) {
                    Row result;
                    bool same_bound_type = false;
                    result.elements.reserve(m_columns.size()-1); // REVIEW: or minimum with pivot.size+other.size?
                    Rational pivot_scale;
                    Rational other_scale;
                    // TODO: durch delta Zeug ersetzen?
                    if (m_rows[pivot_row].relation == carl::Relation::LEQ) {
                        result.relation = m_rows[other_row].relation;
                    } else if (((pivot_coeff > 0) && (other_coeff > 0)) || ((pivot_coeff < 0) && (other_coeff < 0))) {
                        result.relation = carl::Relation::LEQ;
                    } else { // todo: take EQ into account
                        result.relation = carl::Relation::LESS;
                    }
                    // REVIEW: skalierung anpassen? Nur mit Integers arbeiten?
                    if (pivot_coeff > 0) {
                        pivot_scale = -other_coeff;
                        other_scale = pivot_coeff;
                        if (other_coeff > 0) {
                            same_bound_type = true;
                        }
                    } else { // pivot_coeff < 0
                        pivot_scale = other_coeff;
                        other_scale = -pivot_coeff;
                        if (other_coeff < 0) {
                            same_bound_type = true;
                        }
                    }

                    std::vector<RowElement>::const_iterator pivot_iter = m_rows[pivot_row].elements.begin();
                    std::vector<RowElement>::const_iterator other_iter = m_rows[other_row].elements.begin();
                    std::vector<RowElement>::const_iterator pivot_end = m_rows[pivot_row].elements.end();
                    std::vector<RowElement>::const_iterator other_end = m_rows[other_row].elements.end();
                    while((pivot_iter != pivot_end) && (other_iter != other_end)) {
                        if (pivot_iter->column < other_iter->column) {
                            result.elements.emplace_back(pivot_iter->column, pivot_scale*(pivot_iter->value));
                            pivot_iter++;
                        } else if (pivot_iter->column > other_iter->column) {
                            result.elements.emplace_back(other_iter->column, other_scale*(other_iter->value));
                            other_iter++;
                        } else { // same column
                            if (pivot_iter->column != eliminated_col) { // we know that the eliminated colum will be zero
                                Rational value = other_scale*(other_iter->value) + pivot_scale*(pivot_iter->value);
                                if (!carl::is_zero(value)) result.elements.emplace_back(pivot_iter->column, value);
                            }
                            pivot_iter++;
                            other_iter++;
                        }
                    }
                    return std::make_pair(result, same_bound_type);
                }

                struct GaussPivot {
                    RowIndex row;
                    ColumnIndex col;
                    Rational coeff;
                    GaussPivot(RowIndex _row, ColumnIndex _col, Rational _coeff) : row(_row), col(_col), coeff(_coeff) {}
                };

                void apply_gauss_step(GaussPivot pivot, const std::set<RowIndex>& inactive_equalities) { // TODO: columns are incorrect after this
                    Column col = m_columns.at(pivot.col);
                    for (const ColumnElement& ce : col) {
                        if (inactive_equalities.count(ce.row) == 1) continue;
                        Row result;
                        result.elements.reserve(m_columns.size()-1); // REVIEW: or minimum with pivot.size+other.size?
                        Rational pivot_scale;
                        Rational other_scale;
                        result.relation = m_rows[ce.row].relation;
                        // REVIEW: skalierung anpassen? Nur mit Integers arbeiten?
                        if (pivot.coeff > 0) {
                            pivot_scale = -value_at(ce);
                            other_scale = pivot.coeff;
                        } else { // pivot_coeff < 0
                            pivot_scale = value_at(ce);
                            other_scale = -pivot.coeff;
                        }

                        std::vector<RowElement>::const_iterator pivot_iter = m_rows[pivot.row].elements.begin();
                        std::vector<RowElement>::const_iterator other_iter = m_rows[ce.row].elements.begin();
                        std::vector<RowElement>::const_iterator pivot_end = m_rows[pivot.row].elements.end();
                        std::vector<RowElement>::const_iterator other_end = m_rows[ce.row].elements.end();
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
                        m_rows[ce.row] = result; // REVIEW: is there a better in-place assignment?
                    }
                }

                std::optional<GaussPivot> choose_gaussian_pivot(const std::set<RowIndex>& inactive_rows) {
                    // TODO: use heuristics
                    for (const RowIndex r : m_equalities) {
                        if (inactive_rows.count(r) == 1) continue;
                        ColumnIndex c = m_rows[r].elements[0].column;
                        if (c < m_rhs_index) return GaussPivot(r,c,m_rows[r].elements[0].value);
                    }
                    return std::nullopt;
                }

                void apply_gaussian_elimination() {
                    std::set<RowIndex> used_equalities;
                    std::optional<GaussPivot> pivot = choose_gaussian_pivot(used_equalities);
                    while (pivot) {
                        used_equalities.emplace(pivot->row);
                        apply_gauss_step(*pivot, used_equalities);
                        pivot = choose_gaussian_pivot(used_equalities);
                    }
                }

                FMPlexTableau restrict_to_inequalities() {
                    FMPlexTableau result(m_inequalities.size(), m_rhs_index);
                    for (RowIndex i : m_inequalities) {
                        result.append_row(m_rows[i]);
                    }
                    return result;
                }

                std::vector<ColumnIndex> non_zero_variable_columns() const {
                    std::vector<ColumnIndex> result;
                    for (std::map<ColumnIndex, Column>::const_iterator it = m_columns.begin(); it != m_columns.end(); it++) {
                        if (it->first >= m_rhs_index) break;
                        result.push_back(it->first);
                    }
                    return result;
                }

                ColumnIndex first_non_zero_column(RowIndex r) const {
                    return m_rows[r].elements[0].column;
                }

                std::vector<ColumnIndex> non_zero_variable_columns(const RowIndex r) const {
                    std::vector<ColumnIndex> result;
                    for (const RowElement& re : m_rows[r].elements) {
                        result.push_back(re.column);
                    }
                    return result;
                }

                // NOTE: assumes that values not in m are 0
                Rational bound_value(const RowIndex row, ColumnIndex elim_col_index, const std::map<std::size_t, Rational>& m) const {
                    Rational bound(0);
                    Rational coeff;
                    for (const auto& row_elem : m_rows[row].elements) {
                        if (row_elem.column > m_rhs_index) break;
                        else if (row_elem.column == m_rhs_index) bound = bound + row_elem.value;
                        else if (row_elem.column != elim_col_index) {
                            auto it = m.find(row_elem.column);
                            if (it != m.end()) bound = bound - (row_elem.value * (it->second));
                        }
                        else coeff = row_elem.value;
                    }
                    bound = bound / coeff;
                    return bound;
                }

                bool is_lhs_zero() const {
                    // if the first non-zero column is the rhs (or one of the lin comb columns)
                    return (m_columns.begin()->first) >= m_rhs_index;
                }
        };

    } // namespace fmplex
} // namespace smtrat