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

enum class bound { infty };
struct cell_at_level {
private: 
    enum class type { section, sector };

    std::optional<indexed_root> m_lower;
    std::optional<indexed_root> m_upper;
    type m_type;

public:

    cell_at_level(indexed_root bound) : m_lower(bound), m_type(type::section) {}
    cell_at_level(indexed_root lower, indexed_root upper) : m_lower(lower), m_upper(upper), m_type(type::sector) {}
    cell_at_level(bound lower, indexed_root upper) : m_upper(upper), m_type(type::sector) {}
    cell_at_level(indexed_root lower, bound upper) : m_lower(lower), m_type(type::sector) {}

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

}