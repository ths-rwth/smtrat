#pragma once

#include "../common.h"
#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

struct indexed_root {
    poly_ref poly;
    size_t index;
};
std::ostream& operator<<(std::ostream& os, const indexed_root& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

enum class bound { infty };
class cell {
    enum class type { section, sector };

    std::optional<indexed_root> m_lower;
    std::optional<indexed_root> m_upper;
    type m_type;

public:

    cell(indexed_root bound) : m_lower(bound), m_type(type::section) {}
    cell(indexed_root lower, indexed_root upper) : m_lower(lower), m_upper(upper), m_type(type::sector) {}
    cell(bound lower, indexed_root upper) : m_upper(upper), m_type(type::sector) {}
    cell(indexed_root lower, bound upper) : m_lower(lower), m_type(type::sector) {}

    bool is_sector() const {
        return m_type == type::sector;
    }

    bool is_section() const {
        return m_type == type::section;
    }

    indexed_root sector_defining() const {
        assert(is_sector());
        return *m_lower;
    }

    auto lower() const {
        return m_lower;
    }

    auto upper() const {
        return m_upper;
    }
};

class covering {
    std::vector<cell> m_data;

public:
    void add(const cell& c) {
        assert(!m_data.empty() || (c.is_sector() && !c.lower()));
        assert(m_data.empty() || c.lower());
        assert(m_data.empty() || m_data.back().upper());
        assert(m_data.empty() || *m_data.back().upper() <= *c.lower());
        assert(m_data.empty() || !m_data.back().lower() || *m_data.back().lower() <= *c.lower());
        m_data.push_back(c);
    }

    const auto& cells() {
        return m_data;
    }
};

class indexed_root_ordering {
    std::vector<std::pair<indexed_root, indexed_root>> m_data_below;
    std::vector<std::pair<indexed_root, indexed_root>> m_data_above;

    void add(std::vector<std::pair<indexed_root, indexed_root>>& data, indexed_root first, indexed_root second) {
        assert(first.poly.level == second.poly.level && first != second);
        data.push_back(std::make_pair(first, second));
    }

public:
    /**
     * first is the root closer to the lower bound
     * 
     * relations need to be added in descending order of the first elements
     */
    void add_below_cell(indexed_root first, indexed_root second) {
        return add(m_data_below, first, second);
    }

    /**
     * first is the root closer to the upper bound
     * 
     * relations need to be added in ascending order of the first elements
     */
    void add_above_cell(indexed_root first, indexed_root second) {
        return add(m_data_above, first, second);
    }

    const auto& data_below() const {
        return m_data_below;
    }

    const auto& data_above() const {
        return m_data_above;
    }
};

}