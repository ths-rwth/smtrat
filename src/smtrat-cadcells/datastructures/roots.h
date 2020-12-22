#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

struct indexed_root {
    poly_ref poly;
    size_t index;
};
std::ostream& operator<<(std::ostream& os, const indexed_root& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

// TODO rename to region?
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

// TODO:

class indexed_root_ordering {
    std::vector<std::pair<indexed_root, indexed_root>> m_data;

public:
    void add(indexed_root first, indexed_root second) {
        assert(first.poly.level == second.poly.level && first != second);
        if (first.poly.id > second.poly.id || (first.poly.id == second.poly.id && first.index > second.index)) {
            return add_relation(second, first);
        }
        m_data.push_back(std::make_pair(first, second));
    }

    const auto& relation() const {
        return m_data;
    }
};

struct representative {
    cell interval;
    indexed_root_ordering ordering;
    std::vector<poly_ref> equational;
};

}