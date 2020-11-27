#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

#include "polynomials.h"

namespace smtrat::cadcells::datastructures {

namespace detail {

template<typename ... Ts>
struct prop_sets {};

template <class T, class... Ts>
struct prop_sets<T, Ts...> : prop_sets<Ts...> {
  // prop_set(T t, Ts... ts) : prop_set<Ts...>(ts...), content(t) {}
  std::set<T> content;
};

template <class T, class... Ts>
std::set<T>& get(prop_sets<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts>
typename std::disable_if<std::is_same<S, T>::value>::type 
std::set<S>& get(prop_sets<T, Ts...>& sets) {
    prop_sets<Ts...>& base = sets;
    return get<S>(base);
}

}

template<typename ... Ts>
class properties {
    const poly_pool& m_polynomials;
    size_t m_level;
    std::shared_ptr<properties<Ts...>> m_lower; 
    detail::prop_sets<Ts...> m_properties;

private:
    template<typename P>
    void insert_at_level(size_t level, P&& property) {
        assert(level <= m_level);
        if (level < m_level) {
            assert(level > 0);
            assert(m_lower != std::nullptr);
            m_lower->insert_at_level(level, std::move(property));
        } else {
            get<P>(m_properties).emplace(std::move(property));
        }
    }

public:
    properties(const poly_pool& polynomials, size_t level) : m_polynomials(polynomials), m_level(level) {
        if (level > 0) {
            m_lower = std::make_shared<properties>(m_polynomials, level-1);
        }
    }
    properties(const poly_pool& polynomials, size_t level, std::shared_ptr<properties> lower) : properties(polynomials, level), m_lower(lower) {}

    size_t level() { return m_level; }
    auto lower() { return m_lower; }

    template<typename P>
    void insert(P&& property) {
        insert_at_level(level_of(m_polynomials.var_order(), property), std::move(property));
    }

    template<typename P>
    const std::set<P> get() {
        return get<P>(prop_sets);
    }

    /*
    void merge(const properties& other) {
        assert(other.m_level == m_level && other.m_var_order = m_var_order);
        // TODO:
        m_properties.insert(other.m_properties.begin(), other.m_properties.end());
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
