#pragma once

#include "../datastructures/polynomials.h"
#include "../datastructures/properties.h"
#include "../datastructures/projections.h"


namespace smtrat::cadcells::operators::mccallum::properties {

struct poly_sgn_inv {
    datastructures::poly_ref poly;   
};
size_t level_of(const datastructures::poly_pool&, const poly_sgn_inv& prop) {
    return prop.poly.level;
}
bool is_trivial(datastructures::projections& proj, const poly_sgn_inv& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_sgn_inv& data) {
    os << data.poly << " si";
    return os;
}

struct poly_irreducible_sgn_inv {
    datastructures::poly_ref poly;   
};
size_t level_of(const datastructures::poly_pool&, const poly_irreducible_sgn_inv& prop) {
    return prop.poly.level;
}
bool is_trivial(datastructures::projections& proj, const poly_irreducible_sgn_inv& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_irreducible_sgn_inv& data) {
    os << data.poly << " si and irreducible";
    return os;
}

struct poly_ord_inv {
    datastructures::poly_ref poly;
};
size_t level_of(const datastructures::poly_pool&, const poly_ord_inv& prop) {
    return prop.poly.level;
}
bool is_trivial(datastructures::projections& proj, const poly_ord_inv& prop) {
    return proj.is_const(prop.poly);
}
std::ostream& operator<<(std::ostream& os, const poly_ord_inv& data) {
    os << data.poly << " oi";
    return os;
}

struct root_well_def {
    datastructures::poly_ref poly;
    size_t idx;   
};
size_t level_of(const datastructures::poly_pool&, const root_well_def& prop) {
    return prop.poly.level - 1;
}
bool is_trivial(datastructures::projections& proj, const root_well_def& prop) {
    return false;
}
std::ostream& operator<<(std::ostream& os, const root_well_def& data) {
    os << data.poly << " well-def";
    return os;
}

struct poly_pdel {
    datastructures::poly_ref poly;
};
size_t level_of(const datastructures::poly_pool&, const poly_pdel& prop) {
    return prop.poly.level - 1;
}
bool is_trivial(datastructures::projections& proj, const poly_pdel& prop) {
    return false;
}
std::ostream& operator<<(std::ostream& os, const poly_pdel& data) {
    os << data.poly << " projectively delineable";
    return os;
}

using properties = datastructures::properties<poly_sgn_inv,poly_sgn_inv,poly_ord_inv,root_well_def,poly_pdel>;

}