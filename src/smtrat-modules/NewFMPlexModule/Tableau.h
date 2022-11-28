#pragma once

namespace smtrat::fmplex {

using ColumnIndex = std::size_t;
using RowIndex = std::size_t;
using ColumnPosition = std::size_t;

using DeltaRational = lra::Value<Rational>;

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

struct Origins {
    std::set<std::size_t> constraint_indices;
    bool non_negative;
};

using Column = std::vector<ColumnElement>;
using ColumnsIterator = std::map<ColumnIndex, Column>::const_iterator;

class FMPlexTableau { // REVIEW: memory management : alle RowElements in einen grossen vector?

    private:
        std::vector<Row> m_rows;                /// vector containing the rows
        std::map<ColumnIndex,Column> m_columns; /// map containing the non-zero columns
        
        ColumnIndex m_rhs_index;                /// the column index of the constraints' right hand side real part
        ColumnIndex m_delta_index;              /// the column index of the constraints' right hand side delta part (rhs_index + 1)
        ColumnIndex m_first_origin_index;       /// the first column index belonging to the lin. comb. (delta_index + 1)

        // REVIEW: is storing this information better than computation on the fly?
        std::vector<RowIndex> m_equalities;     /// vectors of row indices corresponding to the contained equalities
        std::vector<RowIndex> m_disequalities;  /// vectors of row indices corresponding to the contained disequalities
        std::vector<RowIndex> m_inequalities;   /// vectors of row indices corresponding to the contained inequalities

    public:
        // Constructors

        FMPlexTableau(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index);

        FMPlexTableau(std::size_t n_rows, ColumnIndex rhs_index);

        // TODO: destructor? and other constructors?

        // REVIEW: for which of the getters can i return a reference?
        inline std::size_t nr_of_rows() const { return m_rows.size(); }
        inline std::size_t nr_of_equalities() const { return m_equalities.size(); }
        inline std::size_t nr_of_disequalities() const { return m_disequalities.size(); }
        
        inline std::vector<RowIndex> equality_rows() const { return m_equalities; }
        inline std::vector<RowIndex> disequality_rows() const { return m_disequalities; }

        inline ColumnIndex rhs_index() const { return m_rhs_index; }

        inline Rational value_at(const ColumnElement& ce) const {
            return m_rows[ce.row].elements[ce.position_in_row].value;
        }

        inline carl::Relation relation(const RowIndex ri) const { return m_rows[ri].relation; }

        // REVIEW: encapsulation. Maybe define type for iterator...
        inline ColumnsIterator columns_begin() const { return m_columns.begin(); }
        inline ColumnsIterator columns_end() const { return m_columns.end(); }

        inline bool is_lhs_zero() const {
            return (m_columns.begin()->first) >= m_rhs_index;
        }

    private:
        inline std::size_t origin(const ColumnIndex ci) const {
            assert(ci >= m_first_origin_index);
            return ci - m_first_origin_index;
        }

    public:
        Origins origins(const RowIndex ri) const;

        std::vector<ColumnIndex> non_zero_variable_columns() const;
        std::vector<ColumnIndex> non_zero_variable_columns(const RowIndex ri) const;

        ColumnIndex first_non_zero_column(const RowIndex ri) const;

        bool is_row_conflict(const RowIndex ri) const;

        void append_row(const Row& row);

        void copy_row_from(const RowIndex row, const FMPlexTableau& other) {
            append_row(other.m_rows[row]);
        }

        std::pair<Row, bool> combine(const RowIndex pivot_row, const RowIndex other_row,
            const ColumnIndex eliminated_col, const Rational& pivot_coeff, const Rational& other_coeff);

        DeltaRational bound_value(const RowIndex ri, const ColumnIndex ci_eliminated, const std::map<ColumnIndex, DeltaRational>& model) const;

        struct GaussPivot {
            RowIndex row;
            ColumnIndex col;
            Rational coeff;
            GaussPivot(RowIndex _row, ColumnIndex _col, Rational _coeff) : row(_row), col(_col), coeff(_coeff) {}
        };

        /**
            * @brief 
            * 
            * @param pivot 
            * @param inactive_equalities 
            */
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
                // REVIEW: this is also in combine -> refactor?
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

        /**
            * @brief 
            * 
            * @param inactive_rows 
            * @return std::optional<GaussPivot> 
            */
        std::optional<GaussPivot> choose_gaussian_pivot(const std::set<RowIndex>& inactive_rows) {
            // TODO: use heuristics
            for (const RowIndex r : m_equalities) {
                if (inactive_rows.count(r) == 1) continue;
                ColumnIndex c = m_rows[r].elements[0].column;
                if (c < m_rhs_index) return GaussPivot(r,c,m_rows[r].elements[0].value);
            }
            return std::nullopt;
        }

        /**
            * @brief 
            * 
            */
        void apply_gaussian_elimination() {
            std::set<RowIndex> used_equalities;
            std::optional<GaussPivot> pivot = choose_gaussian_pivot(used_equalities);
            while (pivot) {
                used_equalities.emplace(pivot->row);
                apply_gauss_step(*pivot, used_equalities);
                pivot = choose_gaussian_pivot(used_equalities);
            }
        }

        /**
            * @brief 
            * 
            * @return FMPlexTableau 
            */
        FMPlexTableau restrict_to_inequalities() {
            FMPlexTableau result(m_inequalities.size(), m_rhs_index);
            for (RowIndex i : m_inequalities) {
                result.append_row(m_rows[i]);
            }
            return result;
    }
};

FMPlexTableau::FMPlexTableau(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) {
    m_rows.reserve(constraints.size());
    //m_nr_rows = constraints.size();
    m_rhs_index = variable_index.size();
    m_delta_index = m_rhs_index + 1;
    m_first_origin_index = m_delta_index + 1;

    bool remove_strict = false;
    for (RowIndex row = 0; row < constraints.size(); row++) {
        Row current_row;
        const FormulaT& c = constraints[row];
        std::cout << "processing constraint " << c << "\n";

        carl::Relation r = c.constraint().relation();
        remove_strict = (r == carl::Relation::LESS) || (r == carl::Relation::GREATER);
        bool is_inequality = (remove_strict || (r == carl::Relation::LEQ) || (r == carl::Relation::GEQ));
        current_row.relation = is_inequality ? carl::Relation::LEQ : r;

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
        for (const auto e : current_row.elements) std::cout << "v: " << e.value << ", c: " << e.column << " | ";
        std::cout << "relation: " << current_row.relation << "\n"; 
        append_row(current_row);
    }
}

/**
    * @brief Construct a new FMPlexTableau object
    * 
    * @param n_rows 
    * @param rhs_index 
    */
FMPlexTableau::FMPlexTableau(std::size_t n_rows, ColumnIndex rhs_index) {
    m_rows.reserve(n_rows);
    m_rhs_index = rhs_index;
    m_delta_index = m_rhs_index + 1;
    m_first_origin_index = m_delta_index + 1;
    //m_nr_rows = n_rows;
}

Origins FMPlexTableau::origins(const RowIndex ri) const {
    std::set<std::size_t> result;
    bool non_neg = true;
    std::vector<RowElement>::const_iterator row_it = m_rows[ri].elements.end();
    while (row_it != m_rows[ri].elements.begin()) {
        row_it--;
        if (row_it->column < m_first_origin_index) break;
        result.emplace_hint(result.begin(), origin(row_it->column));
        if (row_it->value < 0) non_neg = false;
    }
    return Origins{result, non_neg};
}

std::vector<ColumnIndex> FMPlexTableau::non_zero_variable_columns() const {
    std::vector<ColumnIndex> result;
    for (std::map<ColumnIndex, Column>::const_iterator it = m_columns.begin(); it != m_columns.end(); it++) {
        if (it->first >= m_rhs_index) break;
        result.push_back(it->first);
    }
    return result;
}

ColumnIndex FMPlexTableau::first_non_zero_column(const RowIndex ri) const {
    return m_rows[ri].elements[0].column;
}

std::vector<ColumnIndex> FMPlexTableau::non_zero_variable_columns(const RowIndex ri) const {
    std::vector<ColumnIndex> result;
    for (const RowElement& e : m_rows[ri].elements) {
        result.push_back(e.column);
    }
    return result;
}

bool FMPlexTableau::is_row_conflict(const RowIndex ri) const {
    std::vector<RowElement>::const_iterator row_it = m_rows[ri].elements.begin();
    if (row_it->column < m_rhs_index) {
        // lhs is non-zero (there is a variable left)
        return false;
    } else if (row_it->column <= m_delta_index) {
        // constraint is (0 ~ b) with b != 0 or (0 ~ c*delta)
        // => conflict only if ~ is = or if ~ is not neq and b < 0 respectively c < 0
        if (m_rows[ri].relation == carl::Relation::NEQ) return false;
        if ((m_rows[ri].relation != carl::Relation::EQ) && (row_it->value > 0)) return false;
    } else if ((m_rows[ri].relation == carl::Relation::LEQ) || (m_rows[ri].relation == carl::Relation::EQ)) {
        // constraint is (0 <= 0) or (0 == 0)
        return false;
    }
    return true;
}

void FMPlexTableau::append_row(const Row& row) {
    for (ColumnPosition i = 0; i < row.elements.size(); i++) {
        RowElement r = row.elements[i];
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

std::pair<Row, bool> FMPlexTableau::combine(const RowIndex pivot_row, const RowIndex other_row,
    const ColumnIndex eliminated_col, const Rational& pivot_coeff, const Rational& other_coeff) {
    Row result;
    bool same_bound_type = false;
    result.elements.reserve(m_columns.size()-1); // REVIEW: or minimum with pivot.size+other.size?
    Rational pivot_scale;
    Rational other_scale;

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

DeltaRational FMPlexTableau::bound_value(const RowIndex ri, const ColumnIndex ci_eliminated, const std::map<ColumnIndex, DeltaRational>& model) const {
    DeltaRational bound(0);
    Rational coeff;
    for (const auto& row_elem : m_rows[ri].elements) {
        // we are only interested in the lhs and rhs, not the origins
        if (row_elem.column > m_delta_index) break;
        else if (row_elem.column == m_rhs_index) bound += row_elem.value;
        else if (row_elem.column == m_delta_index) bound += DeltaRational(0,row_elem.value);
        else if (row_elem.column == ci_eliminated) coeff = row_elem.value;
        else {
            auto it = model.find(row_elem.column);
            if (it != model.end()) bound -= ((it->second) * row_elem.value);
        }
    }
    bound = bound / coeff;
    std::cout << "row " << ri << " gives bound " << bound << "\n";
    return bound;
}

} // namespace smtrat::fmplex