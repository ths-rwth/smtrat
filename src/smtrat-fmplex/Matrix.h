#pragma once
#include <vector>
#include <carl-arith/numbers/numbers.h>

namespace smtrat::fmplex {

using Rational = mpq_class;

class Matrix {

// Type definitions ////////////////////////////////////////////////////////////////////////////////
public:
    using RowIndex  = unsigned;
    using ColIndex  = unsigned;
    using DataIndex = unsigned;

    struct RowEntry {
        ColIndex col_index;
        Rational value;
        RowEntry(ColIndex col, const Rational& v) : col_index(col), value(v) {}
    };

    struct ColEntry {
        RowIndex row_index;
        DataIndex position;
    };

    using Column = std::vector<ColEntry>;

// Members /////////////////////////////////////////////////////////////////////////////////////////
private:
    std::vector<RowEntry>  m_data;
    std::vector<DataIndex> m_row_starts;
    std::vector<Column>    m_cols;

// Private methods /////////////////////////////////////////////////////////////////////////////////
private:
    DataIndex row_start_idx(const RowIndex ri) const {
        assert(ri < m_row_starts.size());
        return m_row_starts[ri];
    }

    DataIndex row_end_idx(const RowIndex ri) const {
        return (ri >= (m_row_starts.size() - 1)) ? m_data.size() : m_row_starts[ri+1];
    }

    std::size_t row_size(const RowIndex ri) const {
        return row_end_idx(ri) - row_start_idx(ri);
    }

// Public interfaces ///////////////////////////////////////////////////////////////////////////////
public:
    Matrix() {}

    Matrix(const Matrix& other) = default;
    Matrix(Matrix&& other) = default;

    Matrix(std::size_t expected_rows, std::size_t expected_cols) : m_cols(expected_cols) {
        m_row_starts.reserve(expected_rows);
    }

    ~Matrix() = default;

    Matrix& operator=(const Matrix& other)=default;

    void reserve(std::size_t n) { m_data.reserve(n); }

    std::size_t n_rows() const { return m_row_starts.size(); }
    std::size_t n_cols() const { return m_cols.size(); }

    std::size_t non_zeros_in_col(const ColIndex ci) const { return m_cols[ci].size(); }
    std::size_t non_zeros_in_row(const RowIndex ri) const { return row_end_idx(ri) - row_start_idx(ri); }
    std::size_t non_zeros_total () const { return m_data.size(); }

    Rational coeff(const RowIndex i, const ColIndex j) const {
        DataIndex max = row_end_idx(i);
        for (DataIndex cur = row_start_idx(i); cur < max; ++cur) {
            if (m_data[cur].col_index == j) return m_data[cur].value;
        }
        return Rational(0);
    }


    /**
     * Appends the row contained in the range between begin and end to the matrix.
     * This assumes the inputs to be of the same iterator-like type pointing to RowEntry's.
     * @return the row index of the appended row within the matrix.
    */
    template<typename It>
    RowIndex append_row(const It& begin, const It& end) {
        RowIndex r_idx(m_row_starts.size());
        m_row_starts.push_back(m_data.size());
        for (It it = begin; it != end; ++it) {
            m_cols[it->col_index].push_back(ColEntry {r_idx, static_cast<unsigned>(m_data.size())});
            m_data.push_back(*it);
        }
        return r_idx;
    }


    /**
     * Computes scale_1*A_(i,-) + scale_2*A_(j,-) where i=row_idx_1, j=row_idx_2.
     * @return a vector containing the elements of the computed row.
    */
    std::vector<RowEntry> combine(const RowIndex row_idx_1, const Rational& scale_1,
                                  const RowIndex row_idx_2, const Rational& scale_2) const {
        std::vector<RowEntry> result;
        result.reserve(3*(row_size(row_idx_1) + row_size(row_idx_2))/4); // just an estimation
        DataIndex idx_1  = row_start_idx(row_idx_1);
        DataIndex idx_2  = row_start_idx(row_idx_2);
        DataIndex end_1  = row_end_idx(row_idx_1);
        DataIndex end_2  = row_end_idx(row_idx_2);

        while (idx_1 != end_1 && idx_2 != end_2) {
            if (m_data[idx_1].col_index < m_data[idx_2].col_index) {
                result.emplace_back(m_data[idx_1].col_index, scale_1*m_data[idx_1].value);
                ++idx_1;
            } else if (m_data[idx_2].col_index < m_data[idx_1].col_index) {
                result.emplace_back(m_data[idx_2].col_index, scale_2*m_data[idx_2].value);
                ++idx_2;
            } else {
                Rational new_value = scale_1*m_data[idx_1].value + scale_2*m_data[idx_2].value;
                if (!carl::is_zero(new_value)) {
                    result.emplace_back(m_data[idx_1].col_index, new_value);
                }
                ++idx_1;
                ++idx_2;
            }
        }
        // At most one of the following loops triggers
        for (; idx_1 != end_1; ++idx_1)
            result.emplace_back(m_data[idx_1].col_index, scale_1*m_data[idx_1].value);
        for (; idx_2 != end_2; ++idx_2)
            result.emplace_back(m_data[idx_2].col_index, scale_2*m_data[idx_2].value);

        return result;
    }


// Iterators & Views ///////////////////////////////////////////////////////////////////////////////
public:
    struct row_iterator {
    private:
        const std::vector<RowEntry>& mr_data;
        DataIndex              m_curr;
    public:
        row_iterator(const std::vector<RowEntry>& data, DataIndex idx)
        : mr_data(data), m_curr(idx) {}

        const RowEntry& operator* () const { return mr_data[m_curr]; }
        const RowEntry* operator->() const { return &(operator*()); }

        row_iterator& operator++() { ++m_curr; return *this; }

        bool operator==(const row_iterator& it) const { return m_curr == it.m_curr; }
        bool operator!=(const row_iterator& it) const { return m_curr != it.m_curr; }
    };

    row_iterator row_begin(RowIndex r) const { return row_iterator(m_data, row_start_idx(r)); }
    row_iterator row_end  (RowIndex r) const { return row_iterator(m_data, row_end_idx(r)  ); }

    struct row_view {
    private:
        const Matrix& mr_data;
        RowIndex m_row_id;
    public:
        row_iterator begin() { return mr_data.row_begin(m_row_id); }
        row_iterator end()   { return mr_data.row_end(m_row_id); }
        row_view(const Matrix& m, const RowIndex ri) : mr_data(m), m_row_id(ri) {}
    };

    row_view row_entries(const RowIndex ri) const { return row_view(*this, ri); }


    struct col_iterator {
    private:
        Column::const_iterator m_it;
        const std::vector<RowEntry>& mr_data;
    public:
        col_iterator(Column::const_iterator it, const std::vector<RowEntry>& data)
        : m_it(it), mr_data(data) {}

        const RowEntry& operator* () const { return mr_data[m_it->position]; }
        const RowEntry* operator->() const { return &(operator*()); }
        RowIndex row() const { return m_it->row_index; }

        col_iterator& operator++() { ++m_it; return *this; }

        bool operator==(const col_iterator& other) const { return m_it == other.m_it; }
        bool operator!=(const col_iterator& other) const { return m_it != other.m_it; }
    };

    col_iterator col_begin(ColIndex c) const {return col_iterator(m_cols[c].begin(), m_data);}
    col_iterator col_end  (ColIndex c) const {return col_iterator(m_cols[c].end(),   m_data);}


    struct col_view {
    private:
        const Matrix& mr_data;
        ColIndex m_col_id;
    public:
        col_iterator begin() { return mr_data.col_begin(m_col_id); }
        col_iterator end()   { return mr_data.col_end(m_col_id); }
        col_view(const Matrix& m, const ColIndex ci) : mr_data(m), m_col_id(ci) {}
    };

    col_view col_entries(const ColIndex ci) const { return col_view(*this, ci); }
};


inline void gcd_normalize(std::vector<typename Matrix::RowEntry>& row) {
    Rational gcd = row.front().value.get_num();
    Rational lcm = row.front().value.get_den();
    for (const auto& e : row) {
        gcd = carl::gcd(gcd, e.value.get_num());
        lcm = carl::lcm(lcm, e.value.get_den());
    }
    Rational scale = lcm/gcd;
    if (!carl::is_one(scale)) {
        for (auto& e : row) e.value *= scale;
    }
}


}