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
    template<typename T, typename Implementation>
    struct UnionFindInterface : Implementation
    {
        using Value = typename Implementation::Value;
        using Representative = typename Implementation::Representative;
        using TranslateMap = std::unordered_map<T, Value>;

        UnionFindInterface(TranslateMap & translate)
            : translate(translate)
        {}

        using Implementation::resize;
        using Implementation::introduce_variable;
        using Implementation::find;
        using Implementation::merge;

        template<template<typename> typename Container>
        void resize(Container<T> const& data) noexcept
        {
            translate.clear();
            translate.reserve(data.size());

            Value node = 0;
            for (const auto& val: data) {
                translate.emplace(val, node++);
            }
            resize(data.size());
        }

        void introduce_variable(T const& var) noexcept
        {
            translate.emplace(var, translate.size());
            introduce_variable(translate.size() - 1);
        }

        [[nodiscard]] auto find(T const& val) noexcept -> Representative const&
        {
            return find(translate.at(val));
        }

        void merge(T const& a, T const& b) noexcept
        {
            merge(translate.at(a), translate.at(b));
        }


    private:
        TranslateMap & translate;
    };

    struct UnionFind
    {
        using Value = size_t;
        using Representative = Value;
        using Parents = std::vector<Value>;
        using Ranks = std::vector<size_t>;

        void resize(size_t size) noexcept
        {
            parents.clear();
            parents.resize(size);
            std::iota(parents.begin(), parents.end(), 0);

            ranks.clear();
            ranks.resize(size, 0);
        }

        void introduce_variable(Value const& var) noexcept
        {
            parents.emplace_back(var);
            ranks.emplace_back(0);
        }

        [[nodiscard]] auto find(Value const& val) noexcept -> Representative const&
        {
            if (val != parents[val])
                parents[val] = find(parents[val]);
            return parents[val];
        }

        void merge(Value const& a, Value const& b) noexcept
        {
            auto repr_a = find(a);
            auto repr_b = find(b);
            if (repr_a == repr_b)
                return;
            if (ranks[repr_a] < ranks[repr_b])
                std::swap(repr_a, repr_b);
            parents[repr_b] = repr_a;
            if (ranks[repr_a] == ranks[repr_b])
                ++ranks[repr_a];
        }

    private:
        Parents parents;
        Ranks ranks;
    };
} // namespace smtrat
