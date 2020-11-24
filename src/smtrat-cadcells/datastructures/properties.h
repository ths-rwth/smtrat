#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

// TODO resolve poly_ref

// TODO is this already part of projection?

struct poly_oi {
    poly_ref poly;
    
};
size_t level_of(const var_order& order, const poly_oi& prop) {
    return level_of(order, prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << data.poly << " oi";
    return os;
}

/*

struct disc_oi {
    Poly poly;
};
size_t level_of(const var_order& order, const poly_oi& prop) {
    return level_of(order, prop.poly) - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << "disc(" << data.poly << ") oi";
    return os;
}

struct res_oi {
    Poly poly;
    Poly poly2;
};
size_t level_of(const var_order& order, const poly_oi& prop) {
    return level_of(order, prop.poly) - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << "res(" << data.poly << ", " << data.poly2 << ") oi";
    return os;
}

struct ldcf_si {
    Poly poly;
};
size_t level_of(const var_order& order, const poly_oi& prop) {
    return level_of(order, prop.poly) - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << "ldcf(" << data.poly << ") oi";
    return os;
}
*/

struct poly_si {
    poly_ref poly;   
};
size_t level_of(const var_order& order, const poly_si& prop) {
    return level_of(order, prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " si";
    return os;
}

struct poly_non_null {
    poly_ref poly;   
};
size_t level_of(const var_order& order, const poly_si& prop) {
    return level_of(order, prop.poly) - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " non-null";
    return os;
}

using property = std::variant<poly_oi,poly_si,poly_non_null>;
size_t level_of(const var_order& order, const poly_si& prop) {
    return std::visit([](const auto& p) { return level_of(order, p); }, prop);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    std::visit([](const auto& p) { os << p; }, prop);
    return os;
}


}