#pragma once

#include "../common.h"
#include <set>

namespace smtrat::cadcells::datastructures {

template<typename T>
struct property_hash {
    std::size_t operator()(const T& p) const {
        return p.hash_on_level();
    }
};

template<typename... Ts>
struct properties_t {};
template<typename T>
using properties_t_set = std::unordered_set<T, property_hash<T>>;

template <class T, class... Ts>
struct properties_t<T, Ts...> : properties_t<Ts...> {
    properties_t_set<T> content; 
};

template <class T, class... Ts>
auto& get(properties_t<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
auto& get(properties_t<T, Ts...>& sets) {
    properties_t<Ts...>& base = sets;
    return get<S>(base);
}

template <class T, class... Ts>
const auto& get(const properties_t<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
const auto& get(const properties_t<T, Ts...>& sets) {
    const properties_t<Ts...>& base = sets;
    return get<S>(base);
}

template <class T>
void merge(properties_t<T>& sets_a, const properties_t<T>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());
}

template <class T, class... Ts>
void merge(properties_t<T, Ts...>& sets_a, const properties_t<T, Ts...>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());

    properties_t<Ts...>& base_a = sets_a;
    const properties_t<Ts...>& base_b = sets_b;
    return merge(base_a, base_b);
}

}