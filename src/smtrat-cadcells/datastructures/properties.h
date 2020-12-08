#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <set>

#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

namespace detail {

template<typename ... Ts>
struct prop_sets {};

template <class T, class... Ts>
struct prop_sets<T, Ts...> : prop_sets<Ts...> {
  // prop_set(T t, Ts... ts) : prop_set<Ts...>(ts...), content(t) {}
  std::unordered_set<T> content;
};

template <class T, class... Ts>
std::unordered_set<T>& get(prop_sets<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
std::unordered_set<S>& get(prop_sets<T, Ts...>& sets) {
    prop_sets<Ts...>& base = sets;
    return get<S>(base);
}

}

template<typename ... Ts>
class properties {
    const poly_pool& m_polynomials;
    size_t m_level;
    std::shared_ptr<properties<Ts...>> m_lower; 
    detail::prop_sets<Ts...> m_data;

public:
    properties(const poly_pool& polynomials, size_t level, std::shared_ptr<properties> lower) : m_polynomials(polynomials), m_level(level), m_lower(lower) {}

    properties(const poly_pool& polynomials, size_t level) : properties(polynomials, level, nullptr) {
        if (level > 0) {
            m_lower = std::make_shared<properties>(m_polynomials, level-1);
        }
    }
    

    size_t level() { return m_level; }
    auto lower() { return m_lower; }

    template<typename P>
    void insert(P&& property) {
        assert(level_of(m_polynomials.var_order(), property) <= m_level && level_of(m_polynomials.var_order(), property) > 0);

        if (level_of(m_polynomials.var_order(), property) == m_level) {
            // TODO triviality check
            //if (!is_trivial(m_projections, property)) {
                get<P>(m_data).emplace(std::move(property));
            //}
        } else {
            assert(m_lower != nullptr);
            m_lower->insert(std::move(property));
        }
    }

    template<typename P>
    bool contains(const P& property) {
        assert(level_of(m_polynomials.var_order(), property) <= m_level && level_of(m_polynomials.var_order(), property) > 0);

        if (level_of(m_polynomials.var_order(), property) == m_level) {
            return get<P>(m_data).contains(property);
        } else {
            assert(m_lower != nullptr);
            return m_lower->contains(property);
        }
    }

    template<typename P>
    const std::set<P> get() {
        return get<P>(m_data);
    }

    /*
    void merge(const properties& other) {
        assert(other.m_level == m_level && other.m_var_order = m_var_order);
        // TODO:
        m_data.insert(other.m_data.begin(), other.m_data.end());
        if (level > 0) {
            assert(m_lower != std::nullptr_t && other.m_lower != std::nullptr_t);
            m_lower->merge(*other.m_lower);
        }
    }

    void merge_lower(properties& other) {
        assert(other.m_level == m_level && other.m_var_order = m_var_order);
        if (m_level > 0) {
            assert(m_lower != std::nullptr_t && other.m_lower != std::nullptr_t);
            m_lower.merge(*other.m_lower);
            other.m_lower = m_lower;
        }
    }
    */
};

}