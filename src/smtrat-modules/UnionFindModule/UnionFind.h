/**
 * @file UnionFind.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

namespace smtrat
{
    template<typename T>
    struct UnionFind
    {
        using value_type = T;
        using node_type = size_t;
        using representative = node_type;

        template<template<typename> typename Container>
        void init(Container<T> const& data) noexcept
        {
            translate.reserve(data.size());

            node_type node = 0;
            for (const auto& val: data) {
                translate.emplace(val, node++);
            }

            parents.resize(data.size());
            std::iota(parents.begin(), parents.end(), 0);

            ranks.resize(data.size(), 0);
        }

        [[nodiscard]] auto find(value_type const& val) noexcept -> representative const&
        {
            return find(translate.at(val));
        }

        void merge(value_type const& a, value_type const& b) noexcept
        {
            merge(translate.at(a), translate.at(b));
        }

        std::vector<node_type> classes() noexcept
        {
            compress();

            auto classes = parents;
            std::sort(classes.begin(), classes.end());
            auto last = std::unique(classes.begin(), classes.end());
            classes.erase(last, classes.end());

            return classes;
        }

        [[nodiscard]] auto find(node_type const& val) noexcept ->representative const&
        {
            if (val != parents[val])
                parents[val] = find(parents[val]);
            return parents[val];
        }

        void merge(node_type const& a, node_type const& b) noexcept
        {
            const auto& repr_a = find(a);
            const auto& repr_b = find(b);
            if (repr_a == repr_b)
                return;
            if (ranks[repr_a] < ranks[repr_b])
                std::swap(parents[repr_a], parents[repr_b]);
            parents[repr_b] = repr_a;
            if (ranks[repr_a] == ranks[repr_b])
                ++ranks[repr_a];
        }

        void compress() noexcept
        {
            for (auto &val : parents) {
                parents[val] = find(val);
            }
        }

private:
        std::unordered_map<T, node_type> translate;

        std::vector<node_type> parents;
        std::vector<size_t> ranks;
    };
} // namespace smtrat
