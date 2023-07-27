#pragma once

namespace smtrat::simplex {


/**
 * A Sparse Vector data structure used as base for both Columns and Rows in the simplex Tableau.
 * 
 * The Element type is required to offer
 * - bool is_dead(),
 * - void set_dead(),
 * - std::size_t m_next_free_idx,
 * with the following purpose:
 * If an element is deleted from the sparse vector, it is not destroyed, but marked as "dead".
 * If then a new element is added, it can be first stored in a dead entry instead of creating
 * a new entry.
 */
template<typename Element>
struct SparseVector {
    inline static const std::size_t NO_INDEX = std::numeric_limits<std::size_t>::max();

    std::vector<Element>  m_entries;
    std::size_t           m_alive_entries  =  0;
    std::size_t           m_first_free_idx =  NO_INDEX;
    mutable std::size_t   m_refs           =  0;
    std::size_t num_nonzero_entries() const { return m_alive_entries;  }
    std::size_t num_entries()         const { return m_entries.size(); }
    bool        is_full()             const { return m_first_free_idx == NO_INDEX; }

    SparseVector() : m_entries() {}

    std::pair<Element&, std::size_t> add_entry() {
        m_alive_entries++;

        if (is_full()) {
            m_entries.push_back(Element());
            return {m_entries.back(), num_entries() - 1};
        }

        assert(m_first_free_idx != NO_INDEX);
        std::size_t pos_idx = m_first_free_idx;
        Element& result = m_entries[pos_idx];
        assert(result.is_dead());
        m_first_free_idx = result.m_next_free_idx;
        return {result, pos_idx};
    }

    void del_entry(std::size_t idx) {
        Element& t = m_entries[idx];
        assert(!t.is_dead());
        t.m_next_free_idx = m_first_free_idx;
        t.set_dead();
        m_alive_entries--;
        m_first_free_idx = idx;
        assert(t.is_dead());
    }
};


/**
 * Base class for iterators over SparseVectors.
 * This does not work as an actual iterator as it misses the dereferenciation operator *(),
 * which needs to be defined in implementing child classes.
 */
template<typename Vec>
struct sparse_iterator_base {
    std::size_t m_curr;
    Vec&        m_vec;

    void move_to_used() {
        while ((m_curr < m_vec.num_entries()) && m_vec.m_entries[m_curr].is_dead()) {
            ++m_curr;
        }
    }

    sparse_iterator_base(Vec& v, bool begin) : m_curr(0), m_vec(v) {
        if (begin) move_to_used();
        else m_curr = m_vec.num_entries();
    }

    sparse_iterator_base& operator++()    { ++m_curr; move_to_used(); return *this; }

    bool operator==(sparse_iterator_base const & it) const { return m_curr == it.m_curr; }
    bool operator!=(sparse_iterator_base const & it) const { return m_curr != it.m_curr; }
};


}