/**
 * @file UnionFind.h
 * @author Henrich Lauko <xlauko@mail.muni.cz>
 * @author Dominika Krejci <dominika.krejci@rwth-aachen.de>
 *
 * @version 2018-11-18
 * Created on 2018-11-18.
 */

#pragma once

#include <immer/vector.hpp>

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

        [[nodiscard]] auto find(T const& val) noexcept -> Representative
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

    struct StaticUnionFind
    {
        using Value = size_t;
        using Representative = Value;
        using Parents = std::vector<Value>;
        using Ranks = std::vector<size_t>;

        void resize(size_t size) noexcept
        {
            _parents.clear();
            _parents.resize(size);
            std::iota(_parents.begin(), _parents.end(), 0);

            _ranks.clear();
            _ranks.resize(size, 0);
        }

        void introduce_variable(Value const& var) noexcept
        {
            _parents.emplace_back(var);
            _ranks.emplace_back(0);
        }

        [[nodiscard]] auto find(Value const& val) noexcept -> Representative
        {
            if (val != _parents[val]) {
                _parents[val] = find(_parents[val]);
            }
            return _parents[val];
        }

        void merge(Value const& a, Value const& b) noexcept
        {
            auto ra = find(a);
            auto rb = find(b);
            if (ra == rb)
                return;
            if (_ranks[ra] < _ranks[rb])
                std::swap(ra, rb);
            _parents[rb] = ra;
            if (_ranks[ra] == _ranks[rb])
                ++_ranks[ra];
        }

    private:
        Parents _parents;
        Ranks _ranks;
    };

    struct PersistentUnionFind
    {
        using Value = size_t;
        using Representative = Value;
        using Parents = immer::vector<Value>;
        using Ranks = immer::vector<size_t>;

        void update_parents(Parents const& parents) noexcept
        {
            _parents = parents;
        }

        void update_parents(Parents && parents) noexcept
        {
            _parents = std::move(parents);
        }

        void update_ranks(Ranks const& ranks) noexcept
        {
            _ranks = ranks;
        }

        void update_ranks(Ranks && ranks) noexcept
        {
            _ranks = std::move(ranks);
        }

        template<typename Ps, typename Rs>
        void update(Ps&& parents, Rs&& ranks) noexcept
        {
            update_parents(std::forward<Ps>(parents));
            update_ranks(std::forward<Rs>(ranks));
        }

        Parents resize_parents(size_t size) const noexcept
        {
            Parents parents;
            for (size_t i = 0; i < size; ++i)
                std::move(parents).push_back(i);
            return parents;
        }

        void resize(size_t size) noexcept
        {
            _parents = resize_parents(size);
            _ranks = Ranks(size, 0);
        }

        void introduce_variable(Value const& var) noexcept
        {
            assert(_parents.size() == var);
            _parents = std::move(_parents).push_back(var);
            _ranks = std::move(_ranks).push_back(0);
        }

        using FindState = std::pair<Parents, Representative>;
        FindState find_impl(Parents parents, Value const& i) const noexcept
        {
            auto const& fi = parents[i];
            if (fi == i) {
                return {parents, i};
            } else {
                auto [updated_parents, repr] = find_impl(parents, fi);
                updated_parents = std::move(updated_parents).set(i, repr);
                return {updated_parents, repr};
            }
        }

        Representative find(Value const& val) noexcept
        {
            auto [parents, repr] = find_impl(_parents, val);
            update_parents(std::move(parents));
            return repr;
        }

        PersistentUnionFind merge(Value const& a, Value const& b) noexcept
        {
            auto const& ra = find(a);
            auto const& rb = find(b);
            if (ra != rb) {
                auto const& ranka = _ranks[ra];
                auto const& rankb = _ranks[rb];

                PersistentUnionFind merged;
                if (ranka > rankb) {
                    auto parents = _parents.set(rb, ra);
                    merged.update(std::move(parents), _ranks);
                } else if(ranka < rankb) {
                    auto parents = _parents.set(ra, rb);
                    merged.update(std::move(parents), _ranks);
                } else {
                    auto ranks = _ranks.set(ra, ranka + 1);
                    auto parents = _parents.set(rb, ra);
                    merged.update(std::move(parents), std::move(ranks));
                }

                return merged;
            }

            return *this;
        }

        void dump() const noexcept {
            std::cerr << "Parents:\n";
            for (auto v : _parents) {
                std::cerr << v << ", ";
            }
            std::cerr << '\n';

            std::cerr << "Ranks:\n";
            for (auto v : _ranks) {
                std::cerr << v << ", ";
            }
            std::cerr << "\n\n";
        }

        Parents _parents;
        Ranks _ranks;
    };


    template< typename UnionFind >
    struct Backtrackable : UnionFind // TODO remove inheritence
    {
        using Value = typename UnionFind::Value;
        using Representative = Value;

        using UnionFind::update;

        void resize(size_t size) noexcept
        {
            UnionFind::resize(size);
        }

        void introduce_variable(Value const& var) noexcept
        {
            UnionFind::introduce_variable(var);
        }

        [[nodiscard]] auto find(Value const& val) noexcept -> Representative
        {
            return UnionFind::find(val);
        }

        void merge(Value const& a, Value const& b) noexcept
        {
            if constexpr ( std::is_void_v< decltype( UnionFind::merge(a, b) ) > ) {
                UnionFind::merge(a, b);
            } else {
                auto updated = UnionFind::merge(a, b);
                update(std::move(updated._parents), std::move(updated._ranks));
            }
            // TODO maintain history
        }

        using Timestamp = std::pair<Value, Value>;

        UnionFind& current() noexcept { return history.back().second; }
        Timestamp& time() noexcept { return history.back().first; }

        std::vector< std::pair< Timestamp, UnionFind > > history;
    };

} // namespace smtrat
