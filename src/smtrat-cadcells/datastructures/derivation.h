#pragma once

#include "../common.h"

#include "polynomials.h"
#include "properties.h"
#include "projections.h"
#include "delineation.h"

namespace smtrat::cadcells::datastructures { // TODO refactor (tidy up pseudo-polymorphism)

template<typename Properties>
class base_derivation;

template<typename Properties>
class sampled_derivation;

template<typename Properties>
using base_derivation_ref = std::shared_ptr<base_derivation<Properties>>;

template<typename Properties>
using sampled_derivation_ref = std::shared_ptr<sampled_derivation<Properties>>;

template<typename Properties>
using derivation_ref = std::variant<base_derivation_ref<Properties>, sampled_derivation_ref<Properties>>;

template<typename Properties>
base_derivation_ref<Properties> base_of(derivation_ref<Properties>& derivation) {
    if (std::holds_alternative<base_derivation_ref<Properties>>(derivation)) {
        return std::get<base_derivation_ref<Properties>>(derivation);
    } else {
        return std::get<sampled_derivation_ref<Properties>>(derivation)->base();
    }
}

template<typename Properties>
const base_derivation_ref<Properties> base_of(const derivation_ref<Properties>& derivation) {
    if (std::holds_alternative<base_derivation_ref<Properties>>(derivation)) {
        return std::get<base_derivation_ref<Properties>>(derivation);
    } else {
        return std::get<sampled_derivation_ref<Properties>>(derivation)->base();
    }
}

template<typename Properties>
class base_derivation {
    projections& m_projections;

    size_t m_level;
    Properties m_properties;
    delineation m_delineation;

    derivation_ref<Properties> m_underlying; 

    template<typename P>
    friend void merge_underlying(std::vector<derivation_ref<P>>& derivations);

public:

    // should be private, but does not work with make_shared:
    base_derivation(projections& projections, size_t level, derivation_ref<Properties> underlying) : m_projections(projections), m_level(level), m_underlying(underlying) {
        assert(level == 0 && underlying == std::nullptr || level > 0 && underlying != std::nullptr);
    }

    auto& polys() { return m_projections.polys(); }
    auto& proj() { return m_projections; }
    auto main_var() {
        if (m_level == 0) return carl::Variable::NO_VARIABLE;
        else return polys().var_order()[m_level-1];
    }
    size_t level() { return m_level; }

    auto& underlying() { assert(m_level > 0); return m_underlying; }
    auto& underlying_cell() { assert(m_level > 0); return std::get<sampled_derivation_ref<Properties>>(m_underlying); }
    const assignment& underlying_sample() { assert(m_level > 0); return underlying_cell()->sample(); }

    auto& delin() { return m_delineation; }

    template<typename P>
    void insert(P property) {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            get<P>(m_properties).emplace(property);
        } else {
            assert(m_underlying != nullptr);
            base_of(m_underlying)->insert(property);
        }
    }

    template<typename P>
    bool contains(const P& property) {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            return get<P>(m_properties).find(property) != get<P>(m_properties).end();
        } else {
            assert(m_underlying != nullptr);
            return base_of(m_underlying)->contains(property);
        }
    }

    template<typename P>
    const auto& properties() {
        return get<P>(m_properties);
    }

    void merge_with(const base_derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        assert(m_delineation.empty() && other.m_delineation.empty());
        merge(m_properties, other.m_properties);
        if (m_level > 0) {
            base_of(m_underlying)->merge_with(*base_of(other.m_underlying));
        }
    }
};

template<typename Properties>
class sampled_derivation { // TODO const semantic
    base_derivation_ref<Properties> m_base;
    std::optional<delineation_cell> m_cell;
    assignment m_sample;

public:
    // should be private, but does not work with make_shared
    sampled_derivation(base_derivation_ref<Properties> base, ran main_sample) : m_base(base) {
        m_sample = m_base->underlying_sample();
        m_sample.emplace(m_base->main_var(), main_sample);
    }

    auto& proj() { return m_base->proj(); }
    auto& polys() { return proj().polys(); }
    auto& base() { return m_base; }
    const delineation_cell& cell() { return *m_cell; }

    void delineate_cell() {
        m_cell = base()->delin().delineate_cell(m_sample.at(base()->main_var()));
    }

    const assignment& sample() {
        return m_sample;
    }

    const ran& main_var_sample() {
        return m_sample.at(base()->main_var());
    }

    template<typename P>
    auto contains(const P& p) { return base()->contains(p); }

    template<typename P>
    void insert(P&& p) { base()->insert(p); }

    template<typename P>
    const auto& properties() { return base()->properties(); }

};

template<typename Properties>
derivation_ref<Properties> make_derivation(projections& proj, const assignment& assignment, size_t level) {
    const auto& vars = proj.polys().var_order();

    derivation_ref<Properties> current = std::make_shared<base_derivation<Properties>>(proj, 0, base_derivation_ref<Properties>(nullptr));
    for (size_t i = 1; i <= level; i++) {
        if (assignment.find(vars[level-1]) != assignment.end()) {
            auto base = std::make_shared<base_derivation<Properties>>(proj, level, current);
            current = std::make_shared<sampled_derivation<Properties>>(base, assignment.at(vars[level-1]));
        } else {
            current = std::make_shared<base_derivation<Properties>>(proj, level, current);
        }
    }

    return current;
}

template<typename Properties>
sampled_derivation_ref<Properties> make_sampled_derivation(base_derivation_ref<Properties> delineation, const ran& main_sample) {
    assert(std::holds_alternative<sampled_derivation_ref<Properties>>(delineation->m_underlying));
    auto sampled_der = std::make_shared<sampled_derivation<Properties>>(delineation, main_sample);
    sampled_der->delineate_cell();
    return sampled_der;
}

template<typename Properties>
void merge_underlying(std::vector<derivation_ref<Properties>>& derivations) {
    std::set<base_derivation_ref<Properties>> underlying;
    for (auto& deriv : derivations) {
        underlying.insert(base_of(base_of(deriv)->underlying()));
    }
    assert(!underlying.empty());
    auto first_underlying = *underlying.begin();
    for (auto iter = std::next(underlying.begin()); iter != underlying.end(); iter++) {
        first_underlying->merge_with(**iter);
    }
    for (auto& deriv : derivations) {
        base_of(deriv)->m_underlying = first_underlying;
    }
}


}