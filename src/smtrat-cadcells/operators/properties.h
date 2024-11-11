#pragma once

#include <functional>
#include "../datastructures/polynomials.h"

/**
 * Contains all properties that are stored in a derivation. 
 * 
 * Note that not all properties have a representation here as not all of them are stored but resolved directly in the derivation rules. 
 */
namespace smtrat::cadcells::operators::properties {

struct poly_constraint_truth_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyConstraint constr;
    size_t level() const {
        return constr.lhs.level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(constr.lhs.id);
    }
};
inline bool operator==(const poly_constraint_truth_inv& lhs, const poly_constraint_truth_inv& rhs) {
    return lhs.constr == rhs.constr;
}
inline bool operator<(const poly_constraint_truth_inv& lhs, const poly_constraint_truth_inv& rhs) {
    return lhs.constr < rhs.constr;
}
inline std::ostream& operator<<(std::ostream& os, const poly_constraint_truth_inv& data) {
    os << data.constr << " ti";
    return os;
}

struct iroot_constraint_truth_inv {
    static constexpr bool is_flag = false; 
    datastructures::IndexedRootConstraint constr;
    size_t level() const {
        return constr.bound.poly.level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(constr.bound.poly.id);
    }
};
inline bool operator==(const iroot_constraint_truth_inv& lhs, const iroot_constraint_truth_inv& rhs) {
    return lhs.constr == rhs.constr;
}
inline bool operator<(const iroot_constraint_truth_inv& lhs, const iroot_constraint_truth_inv& rhs) {
    return lhs.constr < rhs.constr;
}
inline std::ostream& operator<<(std::ostream& os, const iroot_constraint_truth_inv& data) {
    os << data.constr << " ti";
    return os;
}

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

struct poly_semi_sgn_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_semi_sgn_inv& lhs, const poly_semi_sgn_inv& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_semi_sgn_inv& lhs, const poly_semi_sgn_inv& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_semi_sgn_inv& data) {
    os << data.poly << " semi-si";
    return os;
}

struct poly_irreducible_semi_sgn_inv {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;   
    size_t level() const {
        return poly.level;
    }
     std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_irreducible_semi_sgn_inv& lhs, const poly_irreducible_semi_sgn_inv& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_irreducible_semi_sgn_inv& lhs, const poly_irreducible_semi_sgn_inv& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_irreducible_semi_sgn_inv& data) {
    os << data.poly << " semi-si and irreducible";
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

struct poly_del {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.base_level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_del& lhs, const poly_del& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_del& lhs, const poly_del& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_del& data) {
    os << data.poly << " delineable";
    return os;
}

struct poly_proj_del {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.base_level;
    }
    std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_proj_del& lhs, const poly_proj_del& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_proj_del& lhs, const poly_proj_del& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_proj_del& data) {
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

struct poly_ord_inv_base {
    static constexpr bool is_flag = false; 
    datastructures::PolyRef poly;
    size_t level() const {
        return poly.level;
    }
     std::size_t hash_on_level() const {
        return std::hash<std::size_t>()(poly.id);
    }
};
inline bool operator==(const poly_ord_inv_base& lhs, const poly_ord_inv_base& rhs) {
    return lhs.poly == rhs.poly;
}
inline bool operator<(const poly_ord_inv_base& lhs, const poly_ord_inv_base& rhs) {
    return lhs.poly < rhs.poly;
}
inline std::ostream& operator<<(std::ostream& os, const poly_ord_inv_base& data) {
    os << data.poly << " ord inv base";
    return os;
}

struct root_ordering_holds {
    static constexpr bool is_flag = false; 
    datastructures::IndexedRootOrdering ordering;
    std::size_t lvl;
    size_t level() const {
        return lvl;
    }
    std::size_t hash_on_level() const {
        return ordering.data().size();
        // auto hasher = std::hash<std::size_t>();
        // std::size_t seed = ordering.data().size();
        // for(auto& i : ordering.data()) {
        //     std::size_t subseed = 0;
        //     subseed ^= hasher(i.first.poly.id) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        //     subseed ^= hasher(i.first.index) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        //     subseed ^= hasher(i.second.poly.id) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        //     subseed ^= hasher(i.second.index) + 0x9e3779b9 + (seed<<6) + (seed>>2);
        //     seed ^= subseed + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        // }
        // return seed;
    }
};
inline bool operator==(const root_ordering_holds& lhs, const root_ordering_holds& rhs) {
    return lhs.ordering.data() == rhs.ordering.data();
}
inline bool operator<(const root_ordering_holds& lhs, const root_ordering_holds& rhs) {
    return lhs.ordering.data() < rhs.ordering.data();
}
inline std::ostream& operator<<(std::ostream& os, const root_ordering_holds& data) {
    os << data.ordering << " holds";
    return os;
}

}