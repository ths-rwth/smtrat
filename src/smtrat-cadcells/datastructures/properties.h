#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

struct poly_oi {
    Poly poly;
    
};
size_t level_of(const var_order& order, const poly_oi& prop) {
    return level_of(order, prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << data.poly << " oi";
    return os;
}

struct poly_si {
    Poly poly;   
};
size_t level_of(const var_order& order, const poly_si& prop) {
    return level_of(order, prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " si";
    return os;
}

using property = std::variant<poly_oi,poly_si>;
size_t level_of(const var_order& order, const poly_si& prop) {
    return std::visit([](const auto& p) { return level_of(order, p); }, prop);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    std::visit([](const auto& p) { os << p; }, prop);
    return os;
}


}