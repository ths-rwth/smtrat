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

        using Implementation::introduce_variable;
        using Implementation::find;
        using Implementation::merge;
        using Implementation::backtrack;

        void introduce_variable(T const& var) noexcept
        {
            translate.try_emplace(var, translate.size());
            introduce_variable(translate[var]);
        }

        [[nodiscard]] auto find(T const& val) noexcept -> Representative
        {
            return find(translate.at(val));
        }

        void merge(T const& a, T const& b) noexcept
        {
            merge(translate.at(a), translate.at(b));
        }

        void backtrack(T const& a, T const& b) noexcept
        {
            backtrack(translate.at(a), translate.at(b));
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

        void introduce_variable(Value const& var) noexcept
        {
            if ( _parents.size() < var ) {
                _parents.emplace_back(var);
                _ranks.emplace_back(0);
            }
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

        void introduce_variable(Value const& var) noexcept
        {
            for (size_t i = _parents.size(); i <= var; ++i) {
                _parents = std::move(_parents).push_back(i);
                _ranks = std::move(_ranks).push_back(0);
            }
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
    struct Backtrackable
    {
        using Value = typename UnionFind::Value;
        using Representative = Value;

        Backtrackable()
        {
            history.emplace_back( origin(), UnionFind{} );
        }

        void introduce_variable(Value const& var) noexcept
        {
            current().introduce_variable(var);
        }

        [[nodiscard]] auto find(Value const& val) noexcept -> Representative
        {
            return current().find(val);
        }

        void merge(Value const& a, Value const& b) noexcept
        {
            history.emplace_back( Timestamp(a, b), current().merge(a, b) );
        }

        void backtrack(Value const& a, Value const& b) noexcept
        {
            auto ver = version(Timestamp(a, b));
            history.erase(ver, history.end());
        }

        using Timestamp = std::pair<Value, Value>;
        using History = std::vector< std::pair< Timestamp, UnionFind > >;

        [[nodiscard]] auto version(Timestamp && ts) const noexcept -> typename History::const_iterator
        {
            auto it = std::find_if(history.rbegin(), history.rend(), [&] (auto const& ver) {
                return ver.first == ts;
            });

            assert(it != history.rend());
            return std::next(it).base();
        }

        constexpr auto origin() const noexcept -> Timestamp
        {
            constexpr auto t = std::numeric_limits<Value>::max();
            return {t, t};
        }

        UnionFind& current() noexcept { return history.back().second; }

        History history;
    };

} // namespace smtrat
