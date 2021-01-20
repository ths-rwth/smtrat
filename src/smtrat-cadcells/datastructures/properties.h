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
struct properties {};

template <class T, class... Ts>
struct properties<T, Ts...> : properties<Ts...> {
    std::unordered_set<T, property_hash<T>> content; 
};

template <class T, class... Ts>
auto& get(properties<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
auto& get(properties<T, Ts...>& sets) {
    properties<Ts...>& base = sets;
    return get<S>(base);
}

template <class T>
void merge(properties<T>& sets_a, const properties<T>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());
}

template <class T, class... Ts>
void merge(properties<T, Ts...>& sets_a, const properties<T, Ts...>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());

    properties<Ts...>& base_a = sets_a;
    const properties<Ts...>& base_b = sets_b;
    return merge(base_a, base_b);
}

}