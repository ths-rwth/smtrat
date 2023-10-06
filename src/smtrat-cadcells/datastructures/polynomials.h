#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <boost/intrusive/set.hpp>
#include "../OCApproximationStatistics.h"

namespace smtrat::cadcells::datastructures {

/**
 * Refers to a polynomial. 
 */
struct PolyRef {
    /// The level of the polynomial.
    size_t level;
    /// The id of the polynomial with respect to its level.
    size_t id;
    /// The base level of the polynomial.
    size_t base_level;
};
inline bool operator<(const PolyRef& lhs, const PolyRef& rhs) {
    return lhs.level < rhs.level  || (lhs.level == rhs.level && lhs.id < rhs.id);
}
inline bool operator==(const PolyRef& lhs, const PolyRef& rhs) {
    return lhs.level == rhs.level && lhs.id == rhs.id;
}
inline bool operator!=(const PolyRef& lhs, const PolyRef& rhs) {
    return !(lhs == rhs);
}

inline std::ostream& operator<<(std::ostream& os, const PolyRef& data) {
    os << "(" << data.level << " " << data.id << ")";
    return os;
}

auto base_level(Polynomial poly) {
    std::size_t lvl = 0;
    for (std::size_t i = 0; i < poly.context().variable_ordering().size(); i++) {
        if (poly.context().variable_ordering()[i] == poly.main_var()) break;
        if (poly.has(poly.context().variable_ordering()[i])) lvl = i+1;
    }
    return lvl;
}

/**
 * A pool for polynomials.
 * 
 * The polynomials are stored in a table, that is, a list of lists of polynomials of a given level.
 */
class PolyPool {
    struct Element : public boost::intrusive::set_base_hook<> {
        Polynomial poly;
        size_t id;
        Element(Polynomial&& p, size_t i) : poly(p), id(i) {}
        friend bool operator<(const Element& e1, const Element& e2) {
            return e1.poly < e2.poly;
        }
    };
    struct element_less {
        bool operator()(const Polynomial& poly, const Element& element) const { 
            return poly < element.poly;
        }
        bool operator()(const Element& element, const Polynomial& poly) const {
            return element.poly < poly;
        }
    };

    typedef boost::intrusive::set<Element> ElementSet;

    Polynomial::ContextType m_context;
    const VariableOrdering& m_var_order;

    std::vector<std::vector<std::unique_ptr<Element>>> m_polys;
    std::vector<ElementSet> m_poly_ids;

    inline PolyRef negative_poly_ref() const { return PolyRef {0, 0, 0}; }
    inline PolyRef zero_poly_ref() const { return PolyRef {0, 1, 0}; }
    inline PolyRef positive_poly_ref() const { return PolyRef {0, 2, 0}; }
    Polynomial negative_poly;
    Polynomial zero_poly;
    Polynomial positive_poly;

public:
    /**
     * Constructs a polynomial pool with respect to a variable ordering.
     * 
     * @param var_order The variable ordering determining polynomial levels.
     */
    PolyPool(const Polynomial::ContextType& context) : m_context(context), m_var_order(context.variable_ordering()), negative_poly(Polynomial(m_context, -1)), zero_poly(Polynomial(m_context, 0)), positive_poly(Polynomial(m_context, 1)) {
        for (size_t i = 0; i < m_var_order.size(); i++) {
            m_polys.emplace_back();
            m_poly_ids.emplace_back();
        } // why not use resize?
    }

    const VariableOrdering& var_order() const { return m_var_order; }

    PolyRef insert(const Polynomial& poly) {
        auto npoly = poly.normalized();
        PolyRef ref;
        ref.level = carl::level_of(npoly);
        if (ref.level == 0) {
            assert(carl::is_constant(poly));
            if (carl::is_zero(poly)) return zero_poly_ref();
            else if (carl::is_negative(poly.constant_part())) return negative_poly_ref();
            else return positive_poly_ref();
        }
        ref.base_level = base_level(npoly);
        assert(ref.level <= m_polys.size() && ref.level > 0);
        typename ElementSet::insert_commit_data insert_data;
        auto res = m_poly_ids[ref.level-1].insert_check(npoly, element_less(), insert_data);
        if (!res.second) {
            ref.id = res.first->id;
        } else {
            ref.id = m_polys[ref.level-1].size();
            m_polys[ref.level-1].push_back(std::make_unique<Element>(std::move(npoly), ref.id));
            m_poly_ids[ref.level-1].insert_commit(*m_polys[ref.level-1].back(), insert_data);
            #ifdef SMTRAT_DEVOPTION_Statistics
                OCApproximationStatistics::get_instance().degree(poly.degree(m_var_order[ref.level-1]));
            #endif         
        }
        return ref;
    }

    PolyRef operator()(const Polynomial& poly) {
        return insert(poly);
    }

    const Polynomial& get(const PolyRef& ref) const {
        assert(ref.level <= m_polys.size());
        if (ref.level == 0) {
            assert(ref.id <=2);
            if (ref.id == negative_poly_ref().id) return negative_poly;
            else if (ref.id == zero_poly_ref().id) return zero_poly;
            else return positive_poly;
        }
        assert(ref.id < m_polys[ref.level-1].size());
        return m_polys[ref.level-1][ref.id]->poly;
    }

    const Polynomial& operator()(const PolyRef& ref) const {
        return get(ref);
    }

    bool known(const Polynomial& poly) const {
        auto npoly = poly.normalized();
        auto level = carl::level_of(npoly);
        auto res = m_poly_ids[level-1].find(npoly, element_less());
        return res != m_poly_ids[level-1].end();
    }

    void clear_levels(size_t level) {
        assert(level > 0);
        if (level > m_polys.size()) return;
        m_poly_ids.erase(m_poly_ids.begin() + (level - 1), m_poly_ids.end());
        m_polys.erase(m_polys.begin() + (level - 1), m_polys.end());
    }

    const Polynomial::ContextType& get_context() const {
        return m_context;
    }

    inline friend std::ostream& operator<<(std::ostream& os, const PolyPool& data) {
        std::size_t lvl_id = 1;
        for (const auto& lvl : data.m_polys) {
            os << std::endl << lvl_id << ":: ";
            for (const auto& p : lvl) {
                os << p->id << ": " << p->poly << "; ";
            }
            lvl_id++;
        }
        return os;
    }
};

}