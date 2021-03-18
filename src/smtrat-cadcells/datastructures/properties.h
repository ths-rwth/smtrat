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
struct PropertiesT {};
template<typename T>
//using PropertiesTSet = std::unordered_set<T, property_hash<T>>;
using PropertiesTSet = std::set<T>;

template <class T, class... Ts>
struct PropertiesT<T, Ts...> : PropertiesT<Ts...> {
    PropertiesTSet<T> content; 
};

template <class T, class... Ts>
auto& get(PropertiesT<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
auto& get(PropertiesT<T, Ts...>& sets) {
    PropertiesT<Ts...>& base = sets;
    return get<S>(base);
}

template <class T, class... Ts>
const auto& get(const PropertiesT<T, Ts...>& sets) {
    return sets.content;
}

template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
const auto& get(const PropertiesT<T, Ts...>& sets) {
    const PropertiesT<Ts...>& base = sets;
    return get<S>(base);
}

template <class T>
void merge(PropertiesT<T>& sets_a, const PropertiesT<T>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());
}

template <class T, class... Ts>
void merge(PropertiesT<T, Ts...>& sets_a, const PropertiesT<T, Ts...>& sets_b) {
    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());

    PropertiesT<Ts...>& base_a = sets_a;
    const PropertiesT<Ts...>& base_b = sets_b;
    return merge(base_a, base_b);
}

}