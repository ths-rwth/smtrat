#pragma once

#include "../datastructures/properties.h"


namespace smtrat::cadcells::operators::mccallum::properties {

struct poly_si {
    poly_ref poly;   
};
size_t level_of(const poly_pool&, const poly_si& prop) {
    return prop.poly.level;
}
bool is_trivial(const projections& proj, const poly_si& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " si";
    return os;
}

struct poly_irreducible_si {
    poly_ref poly;   
};
size_t level_of(const poly_pool&, const poly_irreducible_si& prop) {
    return prop.poly.level;
}
bool is_trivial(const projections& proj, const poly_irreducible_si& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_si& data) {
    os << data.poly << " si and irreducible";
    return os;
}

struct poly_oi {
    poly_ref poly;
};
size_t level_of(const poly_pool&, const poly_oi& prop) {
    return prop.poly.level;
}
bool is_trivial(const projections& proj, const poly_oi& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_oi& data) {
    os << data.poly << " oi";
    return os;
}

struct poly_non_null {
    poly_ref poly;   
};
size_t level_of(const poly_pool&, const poly_non_null& prop) {
    return prop.poly.level - 1;
}
bool is_trivial(const projections& proj, const poly_non_null& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_non_null& data) {
    os << data.poly << " non-null";
    return os;
}

struct root_well_def {
    poly_ref poly;
    size_t idx;   
};
size_t level_of(const poly_pool&, const root_well_def& prop) {
    return prop.poly.level - 1;
}
bool is_trivial(const projections& proj, const root_well_def& prop) {
    return false;
}
std::ostream& operator<<(std::ostream& os, const root_well_def& data) {
    os << data.poly << " well-def";
    return os;
}

struct poly_pdel {
    poly_ref poly;
};
size_t level_of(const poly_pool&, const poly_pdel& prop) {
    return prop.poly.level - 1;
}
bool is_trivial(const projections& proj, const poly_pdel& prop) {
    return false;
}
std::ostream& operator<<(std::ostream& os, const poly_pdel& data) {
    os << data.poly << " projectively delineable";
    return os;
}

using properties = ::datastructures::properties<poly_si,poly_irreducible_si,poly_oi,poly_non_null,root_well_def,poly_pdel>;

}