#pragma once

#include "../datastructures/polynomials.h"

namespace smtrat::cadcells::operators::properties {

struct poly_sgn_inv {
    datastructures::poly_ref poly;
    size_t level() const {
        return poly.level;
    }
};
std::ostream& operator<<(std::ostream& os, const poly_sgn_inv& data) {
    os << data.poly << " si";
    return os;
}

struct poly_irreducible_sgn_inv {
    datastructures::poly_ref poly;   
    size_t level() const {
        return poly.level;
    }
};
std::ostream& operator<<(std::ostream& os, const poly_irreducible_sgn_inv& data) {
    os << data.poly << " si and irreducible";
    return os;
}

struct poly_ord_inv {
    datastructures::poly_ref poly;
    size_t level() const {
        return poly.level;
    }
};
std::ostream& operator<<(std::ostream& os, const poly_ord_inv& data) {
    os << data.poly << " oi";
    return os;
}

struct root_well_def {
    datastructures::indexed_root root;
    size_t level() const {
        return poly.level-1;
    }
};
std::ostream& operator<<(std::ostream& os, const root_well_def& data) {
    os << data.root.poly << " " << data.root.idx << " well-def";
    return os;
}

struct poly_pdel {
    datastructures::poly_ref poly;
    size_t level() const {
        return poly.level-1;
    }
};
std::ostream& operator<<(std::ostream& os, const poly_pdel& data) {
    os << data.poly << " projectively delineable";
    return os;
}

}