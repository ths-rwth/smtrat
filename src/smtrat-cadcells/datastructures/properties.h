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

template<typename T>
//using PropertiesTSet = std::unordered_set<T, property_hash<T>>;
using PropertiesTSet = std::set<T>; // TODO flat_set?

template<typename T, bool is_flag>
struct PropertiesTContent;

template<typename T>
struct PropertiesTContent<T, true> {
    using type = bool;
};

template<typename T>
struct PropertiesTContent<T, false> {
    using type = PropertiesTSet<T>;
};

template<typename... Ts>
struct PropertiesT {};

/**
 * Set of properties. 
 * 
 * This is a recursive template. The list of template parameters specifies the type of properties which can be hold by this set. 
 * 
 */
template <class T, class... Ts>
struct PropertiesT<T, Ts...> : PropertiesT<Ts...> {
    typename PropertiesTContent<T, T::is_flag>::type content;
};

template <class T, class... Ts>
void prop_insert(PropertiesT<T, Ts...>& sets, const T& element) {
    if constexpr (!T::is_flag) {
        sets.content.emplace(element);
    } else {
        sets.content = true;
    }
}
template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
void prop_insert(PropertiesT<T, Ts...>& sets, const S& element) {
    PropertiesT<Ts...>& base = sets;
    prop_insert<S>(base, element);
}

template <class T, class... Ts>
bool prop_has(const PropertiesT<T, Ts...>& sets, const T& element) {
    if constexpr (!T::is_flag) {
        return sets.content.find(element) != sets.content.end();
    } else {
        return sets.content;
    }
    
}
template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
bool prop_has(const PropertiesT<T, Ts...>& sets, const S& element) {
    PropertiesT<Ts...>& base = sets;
    return prop_has<S>(base, element);
}

template <class T, class... Ts>
const auto& prop_get(const PropertiesT<T, Ts...>& sets) {
    return sets.content;
}
template <class S, class T, class... Ts, typename std::enable_if<!std::is_same<S, T>::value>::type>
const auto& prop_get(const PropertiesT<T, Ts...>& sets) {
    const PropertiesT<Ts...>& base = sets;
    return prop_get<S>(base);
}

//template <class T, class... Ts, typename std::enable_if<(sizeof...(Ts) == 0)>::type>
//void merge(PropertiesT<T>& sets_a, const PropertiesT<T>& sets_b) {
//    sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());
//}

//template <class T, class... Ts, typename std::enable_if<(sizeof...(Ts) > 0)>::type>
template <class T, class... Ts>
void merge(PropertiesT<T, Ts...>& sets_a, const PropertiesT<T, Ts...>& sets_b) {
    if constexpr (!T::is_flag) {
        sets_a.content.insert(sets_b.content.begin(), sets_b.content.end());
    } else {
        sets_a.content = sets_a.content || sets_b.content;
    }
    
    if constexpr(sizeof...(Ts) > 0) {
        PropertiesT<Ts...>& base_a = sets_a;
        const PropertiesT<Ts...>& base_b = sets_b;
        return merge(base_a, base_b);
    }
}

}