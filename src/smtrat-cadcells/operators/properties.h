#pragma once

#include <functional>
#include "../datastructures/polynomials.h"

/**
 * Contains all properties that are stored in a derivation. 
 * 
 * Note that not all properties have a representation here as not all of them are stored but resolved directly in the derivation rules. 
 */
namespace smtrat::cadcells::operators::properties {

struct poly_sgn_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_sgn_inv& lhs, const poly_sgn_inv& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_sgn_inv& lhs, const poly_sgn_inv& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_sgn_inv& data) {
    os << data.poly << " si";
    return os;
}

struct poly_irreducible_sgn_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;   
    size_t level() const {
        return poly.level;
    }
     std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_irreducible_sgn_inv& lhs, const poly_irreducible_sgn_inv& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_irreducible_sgn_inv& lhs, const poly_irreducible_sgn_inv& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_irreducible_sgn_inv& data) {
    os << data.poly << " si and irreducible";
    return os;
}

struct poly_ord_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_ord_inv& lhs, const poly_ord_inv& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_ord_inv& lhs, const poly_ord_inv& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_ord_inv& data) {
    os << data.poly << " oi";
    return os;
}

struct root_well_def {
    static constexpr bool is_flag = false; 
    datastructures::IndexedRoot root;
    size_t level() const {
        return root.poly.level-1;
    }
    std::size_t hash_on_level() const {
        auto hasher = std::hash<std::size_t>();
        std::size_t seed = 0;
        seed ^= hasher(root.poly.id) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        seed ^= hasher(root.index) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        return seed;
    }
};
inline bool operator==(const root_well_def& lhs, const root_well_def& rhs) {
    return lhs.root == rhs.root;
}
inline bool operator<(const root_well_def& lhs, const root_well_def& rhs) {
    return lhs.root < rhs.root;
}
inline std::ostream& operator<<(std::ostream& os, const root_well_def& data) {
    os << data.root.poly << " " << data.root.index << " well-def";
    return os;
}

struct poly_pdel {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.level-1;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_pdel& lhs, const poly_pdel& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_pdel& lhs, const poly_pdel& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_pdel& data) {
    os << data.poly << " projectively delineable";
    return os;
}

struct cell_connected {
    static constexpr bool is_flag = true; 
    std::size_t lvl;
    std::size_t level() const {
        return lvl;
    }
    std::size_t hash_on_level() const {
        return 0;
    }
};
inline bool operator==(const cell_connected& lhs, const cell_connected& rhs) {
    return lhs.lvl == rhs.lvl;
}
inline bool operator<(const cell_connected& lhs, const cell_connected& rhs) {
    return lhs.lvl < rhs.lvl;
}
inline std::ostream& operator<<(std::ostream& os, const cell_connected& data) {
    os << data.lvl << " connected";
    return os;
}

}