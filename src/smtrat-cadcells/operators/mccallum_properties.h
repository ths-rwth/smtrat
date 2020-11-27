#pragma once

#include "../datastructures/properties.h"


namespace smtrat::cadcells::operators::mccallum::properties {

struct poly_si {
    poly_ref poly;   
};
size_t level_of(const poly_pool&, const poly_si& prop) {
    return prop.poly.level;
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " si";
    return os;
}

struct poly_oi {
    poly_ref poly;
};
size_t level_of(const poly_pool&, const poly_oi& prop) {
    return prop.poly.level;
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << data.poly << " oi";
    return os;
}

struct poly_non_null {
    poly_ref poly;   
};
size_t level_of(const poly_pool&, const poly_si& prop) {
    return prop.poly.level - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " non-null";
    return os;
}

struct root_well_def {
    poly_ref poly;
    size_t idx;   
};
size_t level_of(const poly_pool&, const poly_si& prop) {
    return prop.poly.level - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " well-def";
    return os;
}

struct poly_pdel {
    poly_ref poly;
};
size_t level_of(const poly_pool&, const poly_si& prop) {
    return prop.poly.level - 1;
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " projectively delineable";
    return os;
}

using properties = ::datastructures::properties<poly_si,poly_oi,poly_non_null,root_well_def,poly_pdel>;

}