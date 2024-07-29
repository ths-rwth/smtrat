#pragma once

#include "Tableau.h"

namespace smtrat::simplex {

/*///////////////////////////////////////////// Rows ////////////////////////////////////////////*/

template<typename T>
void Tableau<T>::Row::compress(std::vector<Column>& cols) {
    std::size_t new_entry_idx = 0;
    std::size_t sz = this->num_entries();
    for (std::size_t curr_entry_idx = 0; curr_entry_idx < sz; curr_entry_idx++) {
        RowEntry& t1 = this->m_entries[curr_entry_idx];
        if (t1.is_dead()) continue;
        if (curr_entry_idx != new_entry_idx) {
            RowEntry& t2 = this->m_entries[new_entry_idx];
            std::swap(t1.m_coeff, t2.m_coeff);
            t2.m_var = t1.m_var;
            t2.m_position_in_col = t1.m_position_in_col;
            assert(!t2.is_dead());
            Column& col = cols[t2.m_var];
            col.m_entries[t2.m_position_in_col].m_position_in_row = new_entry_idx;
        }
        new_entry_idx++;
    }
    assert(new_entry_idx == this->m_alive_entries);
    for (std::size_t i = this->m_alive_entries; i < this->m_entries.size(); ++i) {
        this->m_entries[i].m_coeff = 0; // TODO: something more idiomatic for resetting the coeff?
    }
    this->m_entries.resize(this->m_alive_entries);
    this->m_first_free_idx = DEAD_ID;
}

template<typename T>
void Tableau<T>::Row::compress_if_needed(std::vector<Column>& cols) {
    if ((2 * this->num_nonzero_entries()) < this->num_entries()) compress(cols);
}

/*/////////////////////////////////////////// Columns ///////////////////////////////////////////*/

template<typename T>
void Tableau<T>::Column::compress(std::vector<Row>& rows) {
    std::size_t new_entry_idx  = 0;
    std::size_t sz = this->num_entries();
    for (std::size_t curr_entry_idx  = 0; curr_entry_idx < sz; curr_entry_idx++) {
        ColEntry& e1 = this->m_entries[curr_entry_idx];
        if (e1.is_dead()) continue;
        if (curr_entry_idx != new_entry_idx) {
            this->m_entries[new_entry_idx] = e1;
            Row& r = rows[e1.m_row_id];
            r.m_entries[e1.m_position_in_row].m_position_in_col = new_entry_idx;
        }
        new_entry_idx++;
    }
    assert(new_entry_idx == this->m_alive_entries);
    this->m_entries.resize(this->m_alive_entries);
    this->m_first_free_idx = DEAD_ID;
}

template<typename T>
inline void Tableau<T>::Column::compress_if_needed(std::vector<Row>& rows) {
    if (((2 * this->num_nonzero_entries()) < this->num_entries()) && (this->m_refs == 0)) {
        compress(rows);
    }
}

/*/////////////////////////////////////////// Tableau ///////////////////////////////////////////*/

template<typename T>
Tableau<T>::~Tableau() {}

template<typename T>
void Tableau<T>::save_var_pos(Row& r) {
    std::size_t idx = 0;
    for (const auto& e : r.m_entries) {
        if (!e.is_dead()) {
            m_var_pos[e.m_var] = idx;
            m_var_pos_idx.push_back(e.m_var);
        }
        ++idx;
    }
}

template<typename T>
void Tableau<T>::reset_var_pos() {
    for (std::size_t i = 0; i < m_var_pos_idx.size(); ++i) {
        m_var_pos[m_var_pos_idx[i]] = DEAD_ID;
    }
    m_var_pos_idx.clear();
}

template<typename T>
void Tableau<T>::ensure_var(Variable v) {
    while (m_columns.size() <= v) {
        m_columns.push_back(Column());
        m_var_pos.push_back(DEAD_ID);
    }
}

template<typename T>
typename Tableau<T>::RowID Tableau<T>::mk_row() {
    RowID r = m_rows.size();
    m_rows.push_back(Row());
    return r;
}

template<typename T>
void Tableau<T>::add_var(RowID dst, const T& n, Variable v) {
    if (carl::is_zero(n)) return;

    Row&    r = m_rows[dst];
    Column& c = m_columns[v];
    auto [r_entry, r_idx] = r.add_entry();
    auto [c_entry, c_idx] = c.add_entry();
    r_entry.m_var   = v;
    r_entry.m_coeff = n;
    r_entry.m_position_in_col = c_idx;
    c_entry.m_row_id  = dst;
    c_entry.m_position_in_row = r_idx;
}

/**
 * Set row1 = row1 + row2 * n
*/
template<typename T>
void Tableau<T>::add(RowID row1, const T& n, RowID row2) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "adding row "<< row2 << " times "<< n << " to row "<< row1);

    if (carl::is_zero(n)) return;

    // loop over variables in row2,
    // add terms in row2 to row1.

    Row& r1 = m_rows[row1];
    save_var_pos(r1);
    T tmp(0);

    row_iterator end = row_end(row2);
    for (row_iterator it  = row_begin(row2); it != end; ++it) {
        Variable v = it->m_var;
        std::size_t pos = m_var_pos[v];
        if (pos == DEAD_ID) {
            // variable v is not in row1
            auto [r_entry, row_idx] = r1.add_entry();
            r_entry.m_var   = v;
            r_entry.m_coeff = n * (it->m_coeff);

            Column& c = m_columns[v];
            auto [c_entry, col_idx] = c.add_entry();
            r_entry.m_position_in_col = col_idx;
            c_entry.m_row_id = row1;
            c_entry.m_position_in_row = row_idx;
        } else {
            // variable v is in row1
            RowEntry& r_entry   = r1.m_entries[pos];
            assert(r_entry.m_var == v);
            tmp = n * (it->m_coeff);
            r_entry.m_coeff += tmp;
            if (carl::is_zero(r_entry.m_coeff)) del_row_entry(r1, pos);
        }
    }

    reset_var_pos();
    r1.compress_if_needed(m_columns);
}

template<typename T>
void Tableau<T>::del_row_entry(Row& r, std::size_t pos) {
    SMTRAT_LOG_DEBUG("smtrat.simplex", "deleting row entry with index " << pos);

    RowEntry& r_entry = r.m_entries[pos];
    Variable col_var = r_entry.m_var;
    std::size_t position_in_col = r_entry.m_position_in_col;
    r.del_entry(pos);
    Column& c = m_columns[col_var];
    c.del_entry(position_in_col);
    c.compress_if_needed(m_rows);
}

template<typename T>
void Tableau<T>::mul(RowID r, const T& n) {
    assert(!carl::is_zero(n));
    if (carl::is_one(n)) return;
    for (auto& e : get_row(r)) e.m_coeff *= n;
}

template<typename T>
void Tableau<T>::neg(RowID r) { mul(r, T(-1)); }

template <typename T>
void Tableau<T>::div(RowID r, const T& n) {
    assert(!carl::is_zero(n));
    if (carl::is_one(n)) return;
    for (auto& e : get_row(r)) e.m_coeff /= n;
}

template<typename T>
void Tableau<T>::gcd_normalize(RowID r, T& g) {
    g = T(0);
    row_iterator end = row_end(r);
    for (row_iterator it = row_begin(r); it != end && !carl::is_one(g); ++it) {
        if (!carl::is_integer(it->m_coeff)) {
            g = T(1);
            break;
        }
        if (carl::is_zero(g)) g = it->m_coeff;
        else g = carl::gcd(g, it->m_coeff);
    }
    if (carl::is_zero(g)) g = T(1);
    else if (!carl::is_one(g)) {
        for (auto& e : get_row(r)) e.m_coeff /= g;
    }
}

template<typename T>
const T& Tableau<T>::get_coeff(RowID r, Variable v) {
    for (auto& e : get_row(r))
        if (e.m_var == v) return e.m_coeff;
    return m_zero;
}

}