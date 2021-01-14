#pragma once

#include "../common.h"

#include "polynomials.h"
#include "properties.h"

namespace smtrat::cadcells::datastructures {

template<typename Properties>
using base_derivation_ref = base_derivation_ref;

template<typename Properties>
using cell_derivation_ref = cell_derivation_ref;

using derivation_ref = std::variant<base_derivation_ref, cell_derivation_ref>;

base_derivation_ref base_of(derivation_ref derivation) {
    if (std::holds_alternative<base_derivation_ref>(derivation)) {
        return std::get<base_derivation_ref>(derivation);
    } else {
        return std::get<cell_derivation_ref>(derivation)->base_derivation();
    }
}

template<typename Properties>
class base_derivation {
    projections& m_projections;

    size_t m_level;
    Properties m_properties;
    delineation m_delineation;

    std::optional<derivation_ref> m_underlying; 

    base_derivation(const projections& projections, size_t level, std::shared_ptr<base_derivation> underlying) : m_projections(projections), m_level(level), m_underlying(underlying) {
        assert(level == 0 && underlying == std::nullptr || level > 0 && underlying != std::nullptr);
    }

    friend std::variant<base_derivation_ref, cell_derivation_ref> make_derivation(projections& projections, const assignment& assignment);

public:

    auto& poly_pool() { return m_projections.poly_pool(); }
    auto& proj() { return m_projections; }
    auto main_var() {
        if (m_level == 0) return carl::Variable::NO_VARIABLE;
        else return poly_pool().var_order()[m_level-1];
    }
    size_t level() { return m_level; }

    auto underlying() { assert(m_level > 0); return *m_underlying; }
    auto underlying_cell() { assert(m_level > 0); return std::get<std::shared_ptr<cell_derivation<Ts...>>>(*m_underlying); }
    assignment& underlying_sample() { assert(m_level > 0); return underlying_cell()->sample(); }

    auto& delineation() { return m_delineation; }

    template<typename P>
    void insert(P&& property) {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            get<P>(m_properties).emplace(std::move(property));
        } else {
            assert(m_lower != nullptr);
            m_lower->insert(std::move(property));
        }
    }

    template<typename P>
    bool contains(const P& property) {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            return get<P>(m_properties).contains(property);
        } else {
            assert(m_lower != nullptr);
            return m_lower->contains(property);
        }
    }

    template<typename P>
    const std::set<P> properties() {
        return get<P>(m_properties);
    }

    void merge(const base_derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        assert(m_delineation.empty() && other.m_delineation.empty());
        merge(m_properties, other.m_properties);
        if (m_level > 0) {
            base_of(m_underlying)->merge(base_of(*other.m_underlying));
        }
    }
};

template<typename Properties>
class cell_derivation {
    base_derivation_ref m_base_derivation;
    std::optional<delineation_cell> m_delineation_cell;
    assignment m_sample;

    cell_derivation(base_derivation_ref base_derivation, ran main_sample) : m_base_derivation(projections) {
        m_sample = base_derivation().underlying_sample();
        m_sample->insert(base_derivation().main_var(), main_sample);
    }

    friend std::variant<base_derivation_ref, cell_derivation_ref> make_derivation(projections& projections, const assignment& assignment);
    friend class base_derivation<Properties>;

public:
    auto& proj() { return m_base_derivation.proj(); }
    auto& base_derivation() { return m_base_derivation; }
    const delineation_cell& delineation_cell() { return m_delineation_cell; }

    void delineate_cell() {
        m_delineation_cell = base_derivation().delineation().delineate_cell(m_sample(base_derivation().main_var()));
    }

    const assignment& sample() {
        return m_sample;
    }
};

template<typename Properties>
std::variant<std::shared_ptr<Properties>, cell_derivation_ref> make_derivation(projections& projections, const assignment& assignment, size_t level) {
    const auto& vars = projections.poly_pool().var_order();

    derivation_ref current = make_shared<base_derivation>(proj, 0, std::nullptr);
    for (size_t i = 1; i <= level; i++) {
        if (assignment.find(vars[level-1]) != assignment.end()) {
            auto base = make_shared<base_derivation>(proj, level, current);
            current = make_shared<cell_derivation>(base, assignment[vars[level-1]]);
        } else {
            current = make_shared<base_derivation>(proj, level, current);
        }
    }

    return current;
}

template<typename Properties>
cell_derivation_ref make_cell_derivation(base_derivation_ref delineation, const ran& main_sample) {
    assert(std::holds_alternative<cell_derivation_ref>(delineation->m_underlying));
    auto cell_del = make_shared<cell_derivation>(delineation, main_sample);
    cell_del.delineate_cell();
    return cell_del;
}

template<typename Properties>
void merge_underlying(std::vector<derivation_ref>& derivations) {
    std::set<derivation_ref> underlying;
    for (const auto& deriv : derivations) {
        underlying.insert(base_of(base_of(deriv).underlying()));
    }
    assert(!underlying.empty());
    for (auto iter = underlying.begin()+1; iter != unterlying.end(); iter++) {
        underlying.front().merge(*iter);
    }
    for (const auto& deriv : derivations) {
        base_of(deriv).m_underlying = underlying.front();
    }
}


}