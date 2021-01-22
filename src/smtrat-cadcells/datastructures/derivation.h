#pragma once

#include "../common.h"

#include "polynomials.h"
#include "properties.h"
#include "projections.h"
#include "delineation.h"

namespace smtrat::cadcells::datastructures {

template<typename Properties> class base_derivation;
template<typename Properties> class delineated_derivation;
template<typename Properties> class sampled_derivation;

template<typename Properties>
using base_derivation_ref = std::shared_ptr<base_derivation<Properties>>;
template<typename Properties>
using delineated_derivation_ref = std::shared_ptr<delineated_derivation<Properties>>;

template<typename Properties>
using sampled_derivation_ref = std::shared_ptr<sampled_derivation<Properties>>;

template<typename Properties>
class derivation_ref {
    std::variant<base_derivation_ref<Properties>, delineated_derivation_ref<Properties>, sampled_derivation_ref<Properties>> m_data;

public:
    derivation_ref(const base_derivation_ref<Properties>& data) : m_data(data) {}
    derivation_ref(const delineated_derivation_ref<Properties>& data) : m_data(data) {}
    derivation_ref(const sampled_derivation_ref<Properties>& data) : m_data(data) {}

    bool is_null() const {
        if (std::holds_alternative<base_derivation_ref<Properties>>(m_data)) {
            return std::get<base_derivation_ref<Properties>>(m_data) == nullptr;
        } else if (std::holds_alternative<delineated_derivation_ref<Properties>>(m_data)) {
            return std::get<delineated_derivation_ref<Properties>>(m_data) == nullptr;
        } else {
            return std::get<sampled_derivation_ref<Properties>>(m_data) == nullptr;
        }
    }
    bool is_sampled() const {
        return std::holds_alternative<sampled_derivation_ref<Properties>>(m_data);
    }

    auto& base_ref() {
        if (std::holds_alternative<base_derivation_ref<Properties>>(m_data)) {
            return std::get<base_derivation_ref<Properties>>(m_data);
        } else if (std::holds_alternative<delineated_derivation_ref<Properties>>(m_data)) {
            return std::get<delineated_derivation_ref<Properties>>(m_data)->base();
        } else {
            assert(is_sampled());
            return std::get<sampled_derivation_ref<Properties>>(m_data)->base();
        }
    }
    auto& delineated_ref() {
        if (std::holds_alternative<delineated_derivation_ref<Properties>>(m_data)) {
            return std::get<delineated_derivation_ref<Properties>>(m_data);
        } else {
            assert(is_sampled());
            return std::get<sampled_derivation_ref<Properties>>(m_data)->delineated();
        }
    }
    auto& sampled_ref() {
        assert(is_sampled());
        return std::get<sampled_derivation_ref<Properties>>(m_data);
    }

    const auto& base_ref() const {
        if (std::holds_alternative<base_derivation_ref<Properties>>(m_data)) {
            return std::get<base_derivation_ref<Properties>>(m_data);
        } else if (std::holds_alternative<delineated_derivation_ref<Properties>>(m_data)) {
            return std::get<delineated_derivation_ref<Properties>>(m_data)->base();
        } else {
            assert(is_sampled());
            return std::get<sampled_derivation_ref<Properties>>(m_data)->base();
        }
    }
    const auto& delineated_ref() const {
        if (std::holds_alternative<delineated_derivation_ref<Properties>>(m_data)) {
            return std::get<delineated_derivation_ref<Properties>>(m_data);
        } else {
            assert(is_sampled());
            return std::get<sampled_derivation_ref<Properties>>(m_data)->delineated();
        }
    }
    const auto& sampled_ref() const {
        assert(is_sampled());
        return std::get<sampled_derivation_ref<Properties>>(m_data);
    }

    auto& base() { return *base_ref(); }
    auto& delineated() { return *delineated_ref(); }
    auto& sampled() { return *sampled_ref(); }
    const auto& base() const { return *base_ref(); }
    const auto& delineated() const { return *delineated_ref(); }
    const auto& sampled() const { return *sampled_ref(); }  

    template<typename P>
    friend bool operator==(const derivation_ref<P>& lhs, const derivation_ref<P>& rhs) {
        return lhs.m_data == rhs.m_data;
    }  
    template<typename P>
    friend bool operator<(const derivation_ref<P>& lhs, const derivation_ref<P>& rhs) {
        return lhs.m_data < rhs.m_data;
    }  
};


template<typename Properties>
class base_derivation {
    template<typename P>
    friend void merge_underlying(std::vector<std::reference_wrapper<sampled_derivation<P>>>& derivations);

    derivation_ref<Properties> m_underlying;

    projections& m_projections;

    size_t m_level;
    Properties m_properties;

public:
    // should be private, but does not work with make_shared:
    base_derivation(projections& projections, derivation_ref<Properties> underlying, size_t level) : m_underlying(underlying), m_projections(projections), m_level(level) {
        assert((level == 0 && m_underlying.is_null()) || (level > 0 && !m_underlying.is_null()));
    }

    derivation_ref<Properties>& underlying() { return m_underlying; }
    derivation_ref<Properties>& underlying() const { return m_underlying; }

    poly_pool& polys() { return m_projections.polys(); }
    projections& proj() { return m_projections; }
    carl::Variable main_var() const {
        if (m_level == 0) return carl::Variable::NO_VARIABLE;
        else return m_projections.polys().var_order()[m_level-1];
    }
    size_t level() const { return m_level; }

    template<typename P>
    void insert(P property) {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            get<P>(m_properties).emplace(property);
        } else {
            assert(!m_underlying.is_null());
            m_underlying.base().insert(property);
        }
    }

    template<typename P>
    bool contains(const P& property) const {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            return get<P>(m_properties).find(property) != get<P>(m_properties).end();
        } else {
            assert(!m_underlying.is_null());
            return m_underlying.base().contains(property);
        }
    }
    template<typename P>
    const properties_t_set<P>& properties() const {
        return get<P>(m_properties);
    }

    void merge_with(const base_derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        merge(m_properties, other.m_properties);
        if (m_level > 0) {
            m_underlying.base().merge_with(other.m_underlying.base());
        }
    }
};

template<typename Properties>
class delineated_derivation {
    base_derivation_ref<Properties> m_base;
    delineation m_delineation;

public:
    // should be private, but does not work with make_shared:
    delineated_derivation(base_derivation_ref<Properties> base) : m_base(base) {
        assert(base->level() > 0);
        assert(base->underlying().is_sampled() || base->level() == 1);
    }

    base_derivation_ref<Properties>& base() { return m_base; };
    base_derivation_ref<Properties>& base() const { return m_base; };

    delineation& delin() { return m_delineation; };
    const assignment& underlying_sample() const {
        if(m_base->level() == 1) { return empty_assignment; }
        else {
            return underlying().sampled().sample();
        }
    }

    derivation_ref<Properties>& underlying() { return m_base->underlying(); };
    derivation_ref<Properties>& underlying() const { return m_base->underlying(); };
    poly_pool& polys() { return m_base->polys(); };
    projections& proj() { return m_base->proj(); };
    carl::Variable main_var() const { return m_base->main_var(); };
    size_t level() const { return m_base->level(); };
    template<typename P>
    void insert(P property) { m_base->insert(property); };
    template<typename P>
    bool contains(const P& property) const { return m_base->contains(property); };
    template<typename P>
    const properties_t_set<P>& properties() const { return m_base->template properties<P>(); };

    void merge_with(const delineated_derivation<Properties>& other) { 
        assert(m_delineation.empty() && other.m_delineation.empty());
        m_base->merge_with(*other.m_base);
    };
};

template<typename Properties>
class sampled_derivation {
    delineated_derivation_ref<Properties> m_delineated;
    std::optional<delineation_interval> m_cell;
    assignment m_sample;

public:

    // should be private, but does not work with make_shared
    sampled_derivation(delineated_derivation_ref<Properties> base, ran main_sample) : m_delineated(base) {
        m_sample = m_delineated->underlying_sample();
        m_sample.emplace(m_delineated->main_var(), main_sample);
    }

    delineated_derivation_ref<Properties>& delineated() { return m_delineated; };
    delineated_derivation_ref<Properties>& delineated() const { return m_delineated; };

    const delineation_interval& cell() const { return *m_cell; }
    void delineate_cell() {
        m_cell = m_delineated->delin().delineate_cell(main_var_sample());
    }

    const assignment& sample() const { return m_sample; };
    const ran& main_var_sample() const { return m_sample.at(m_delineated->main_var()); };

    base_derivation_ref<Properties>& base() { return m_delineated->base(); };
    base_derivation_ref<Properties>& base() const { return m_delineated->base(); };
    delineation& delin() { return m_delineated->delin(); };
    const assignment& underlying_sample() const { return m_delineated->underlying_sample(); }
    derivation_ref<Properties>& underlying() { return m_delineated->underlying(); };
    poly_pool& polys() { return m_delineated->polys(); };
    projections& proj() { return m_delineated->proj(); };
    carl::Variable main_var() const { return m_delineated->main_var(); };
    size_t level() const { return m_delineated->level(); };
    template<typename P>
    void insert(P property) { m_delineated->insert(property); };
    template<typename P>
    bool contains(const P& property) const { return m_delineated->contains(property); };
    template<typename P>
    const properties_t_set<P>& properties() const { return m_delineated->template properties<P>(); };

    void merge_with(const sampled_derivation<Properties>& other) {
        assert(!m_cell && other.m_cell);
        m_delineated->merge_with(other);
    };
};

template<typename Properties>
derivation_ref<Properties> make_derivation(projections& proj, const assignment& assignment, size_t level) {
    const auto& vars = proj.polys().var_order();

    derivation_ref<Properties> current = std::make_shared<base_derivation<Properties>>(proj, base_derivation_ref<Properties>(nullptr), 0);
    for (size_t i = 1; i <= level; i++) {
        auto base = std::make_shared<base_derivation<Properties>>(proj, current, i);
        auto delineated = std::make_shared<delineated_derivation<Properties>>(base);
        if (assignment.find(vars[i-1]) != assignment.end()) {
            current = std::make_shared<sampled_derivation<Properties>>(delineated, assignment.at(vars[i-1]));
        } else {
            current = delineated;
        }
    }

    return current;
}

template<typename Properties>
sampled_derivation_ref<Properties> make_sampled_derivation(delineated_derivation_ref<Properties> delineated, const ran& main_sample) {
    auto sampled_der = std::make_shared<sampled_derivation<Properties>>(delineated, main_sample);
    sampled_der->delineate_cell();
    return sampled_der;
}

template<typename Properties>
void merge_underlying(std::vector<std::reference_wrapper<sampled_derivation<Properties>>>& derivations) {
    std::set<derivation_ref<Properties>> underlying;
    for (auto& deriv : derivations) {
        underlying.insert(deriv.get().underlying());
    }
    assert(!underlying.empty());
    auto first_underlying = *underlying.begin();
    for (auto iter = std::next(underlying.begin()); iter != underlying.end(); iter++) {
        first_underlying.base().merge_with(iter->base());
    }
    for (auto& deriv : derivations) {
        deriv.get().base()->m_underlying = first_underlying;
    }
}


}