#pragma once

#include "SparseVector.h"
#include "VariableInfo.h"

namespace smtrat::simplex {

/**
 * Class for representing and performing operations on a simplex tableau.
 * Mostly inspired by z3's simplex.
 * 
 * Stores the values in sparse vectors, each representing a row for a basic variable.
 * Additionally maintains sparse vectors for columns,
 * which indicate the rows containing the actual values.
 * Note that there is a column for each variable, including the basic variables.
 */
template<typename T>
class Tableau {

/*/////////////////////////////////////// Type definitions //////////////////////////////////////*/

public:
    using RowID = std::size_t;

    struct Entry {
        T     m_coeff;
        Variable m_var;

        Entry(T&& c, Variable v) : m_coeff(std::move(c)), m_var(v) {}

        inline const T& coeff() const { return m_coeff; }
        inline Variable   var() const { return m_var;   }
    };

private:

    inline static const std::size_t DEAD_ID = std::numeric_limits<std::size_t>::max();

    struct RowEntry : public Entry {
        union {
            std::size_t m_position_in_col;
            std::size_t m_next_free_idx;
        };
        RowEntry(T && c, Variable v) : Entry(std::move(c), v), m_position_in_col(0) {}
        RowEntry() : Entry(T(), DEAD_ID), m_position_in_col(0) {}
        bool is_dead () const { return Entry::m_var == DEAD_ID; }
        void set_dead()       { Entry::m_var = DEAD_ID; }
    };

    struct ColEntry {
        RowID m_row_id;
        union {
            std::size_t m_position_in_row;
            std::size_t m_next_free_idx;
        };
        ColEntry(int r, int i): m_row_id(r), m_position_in_row(i) {}
        ColEntry(): m_row_id(0), m_position_in_row(0) {}
        bool is_dead () const { return m_row_id == DEAD_ID; }
        void set_dead()       { m_row_id = DEAD_ID; }
    };

    struct Column;

    struct Row : public SparseVector<RowEntry> {
        Row() : SparseVector<RowEntry>() {}
        void compress           (std::vector<Column> & cols);
        void compress_if_needed (std::vector<Column> & cols);
    };

    struct Column : public SparseVector<ColEntry> {
        Column() : SparseVector<ColEntry>() {}
        void compress           (std::vector<Row> & rows);
        void compress_if_needed (std::vector<Row> & rows);
    };

/*/////////////////////////////////////////// Members ///////////////////////////////////////////*/

    std::vector<Row>         m_rows;
    std::vector<Column>      m_columns;      // column for each var, even the basic ones
    std::vector<std::size_t> m_var_pos;      // temporary map : variables -> positions in row
    std::vector<std::size_t> m_var_pos_idx;  // indices in m_var_pos
    T                        m_zero;

/*////////////////////////////////////////// Functions //////////////////////////////////////////*/

    void del_row_entry(Row& r, std::size_t pos);

    void save_var_pos(Row& r);
    void reset_var_pos();

public:

    Tableau(): m_rows(), m_columns(), m_var_pos(), m_var_pos_idx(), m_zero(0) {}
    ~Tableau();

    void ensure_var(Variable v);

    RowID mk_row();

    std::size_t row_size    (RowID r)    const { return m_rows[r].num_nonzero_entries(); }
    std::size_t column_size (Variable v) const { return m_columns[v].num_nonzero_entries(); }

    std::size_t num_vars()    const { return m_columns.size(); }
    std::size_t num_rows()    const { return m_rows.size(); }
    std::size_t num_entries() const {
        std::size_t result = 0;
        for (const auto& r : m_rows) result += r.num_entries();
        return result;
    }

    void add_var(RowID r, const T& n, Variable var);
    void add    (RowID r, const T& n, RowID src);
    void mul    (RowID r, const T& n);
    void div    (RowID r, const T& n);
    void neg    (RowID r);

    void gcd_normalize(RowID r, T& g);

    const T& get_coeff(RowID r, Variable v);

/*//////////////////////////////////// Iterators & Iterables ////////////////////////////////////*/

// Rows

    class row_iterator : public sparse_iterator_base<Row> {
        using Base = sparse_iterator_base<Row>;
        friend class Tableau;
        row_iterator(Row& r, bool begin) : sparse_iterator_base<Row>(r, begin) {}
    public:
        Entry& operator* () const { return Base::m_vec.m_entries[Base::m_curr]; }
        Entry* operator->() const { return &(operator*()); }
    };

    row_iterator row_begin (RowID r) { return row_iterator(m_rows[r], true ); }
    row_iterator row_end   (RowID r) { return row_iterator(m_rows[r], false); }

    class RowEntries {
        friend class Tableau;
        Tableau& t;
        RowID    r;
        RowEntries(Tableau& t, RowID r): t(t), r(r) {}
    public:
        row_iterator begin() { return t.row_begin(r); }
        row_iterator end()   { return t.row_end(r);   }
    };

    RowEntries get_row(RowID r) { return RowEntries(*this, r); }

// Columns

    class col_iterator : public sparse_iterator_base<Column> {
        using Base = sparse_iterator_base<Column>;
        friend class Tableau;
        std::vector<Row>& m_rows;
        col_iterator(Column& c, std::vector<Row>& r, bool begin)
        : sparse_iterator_base<Column>(c, begin), m_rows(r) {
            ++Base::m_vec.m_refs;
        }
    public:
        ~col_iterator() { --Base::m_vec.m_refs; }

        RowID  get_row()       const { return Base::m_vec.m_entries[Base::m_curr].m_row_id; }
        Entry& get_row_entry() const {
            const ColEntry& c = Base::m_vec.m_entries[Base::m_curr];
            return m_rows[c.m_row_id].m_entries[c.m_position_in_row];
        }

        std::pair<RowID, Entry*>  operator* () {
            return std::make_pair(get_row(), &get_row_entry());
        }
    };

    col_iterator col_begin(Variable v) { return col_iterator(m_columns[v], m_rows, true ); }
    col_iterator col_end  (Variable v) { return col_iterator(m_columns[v], m_rows, false); }

    class ColEntries {
        friend class Tableau;
        Tableau& t;
        Variable v;
        ColEntries(Tableau& t, int v): t(t), v(v) {}
    public:
        col_iterator begin() { return t.col_begin(v); }
        col_iterator end()   { return t.col_end(v);   }
    };

    ColEntries get_col(int v) { return ColEntries(*this, v); }

/*/////////////////////////////////////////// Printing //////////////////////////////////////////*/

    void print() {
        assert(false); // not yet implemented
    }
};

}

#include "Tableau.tpp"