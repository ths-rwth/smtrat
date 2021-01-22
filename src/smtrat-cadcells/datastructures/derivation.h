#pragma once

#include "../common.h"

#include "polynomials.h"
#include "properties.h"
#include "projections.h"
#include "delineation.h"

namespace smtrat::cadcells::datastructures { // TODO refactor (tidy up pseudo-polymorphism)

template<typename Base, typename T>
inline bool instance_of(const T *ptr) {
    return dynamic_cast<const Base*>(ptr) != nullptr;
}

template<typename Properties>
class derivation {
public:
    using ref = std::shared_ptr<derivation>;

    virtual derivation<Properties>::ref& underlying() = 0;

    virtual poly_pool& polys() = 0;
    virtual projections& proj() = 0;
    virtual carl::Variable main_var() = 0;
    virtual size_t level() = 0;

    template<typename P>
    virtual void insert(P property) = 0;
    template<typename P>
    virtual bool contains(const P& property) const = 0;
    template<typename P>
    virtual const std::unordered_set<P>& properties() const = 0;

    virtual void merge_with(const derivation<Properties>::ref& other) = 0;
};

template<typename Properties>
class delineated_derivation : derivation {
public:
    using ref = std::shared_ptr<delineated_derivation>;

    virtual derivation<Properties>::ref& base() = 0;

    virtual delineation& delin() = 0;
    virtual const assignment& underlying_sample() const = 0;
};

template<typename Properties>
class sampled_derivation : delineated_derivation {
public:
    using ref = std::shared_ptr<sampled_derivation>;

    virtual delineated_derivation<Properties>::ref& delineated_base() = 0;

    virtual const delineation_cell& cell() const = 0;
    virtual void delineate_cell() = 0;
    virtual const assignment& sample() const = 0;
    virtual const ran& main_var_sample() const = 0;
};


template<typename Properties>
class derivation_impl : public derivation<Properties> {
    derivation<Properties>::ref m_underlying;

    projections& m_projections;

    size_t m_level;
    Properties m_properties;

    /* TODO: 
    template<typename P>
    friend void merge_underlying(std::vector<derivation<P>::ref>& derivations);

    */

public:
    // should be private, but does not work with make_shared:
    derivation_impl(projections& projections, size_t level, derivation<Properties>::ref underlying) : m_projections(projections), m_level(level), m_underlying(underlying) {
        assert(level == 0 && underlying == nullptr || level > 0 && underlying != nullptr);
    }

    derivation<Properties>::ref& underlying() { return m_underlying; }

    poly_pool& polys() { return m_projections.polys(); }
    projections& proj() { return m_projections; }
    carl::Variable main_var() const {
        if (m_level == 0) return carl::Variable::NO_VARIABLE;
        else return polys().var_order()[m_level-1];
    }
    size_t level() const { return m_level; }

    template<typename P>
    void insert(P property) const {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            get<P>(m_properties).emplace(property);
        } else {
            assert(m_underlying != nullptr);
            base_of(m_underlying)->insert(property);
        }
    }

    template<typename P>
    bool contains(const P& property) const {
        assert(property.level() <= m_level && property.level() > 0);

        if (property.level() == m_level) {
            return get<P>(m_properties).find(property) != get<P>(m_properties).end();
        } else {
            assert(m_underlying != nullptr);
            return base_of(m_underlying)->contains(property);
        }
    }
    template<typename P>
    virtual const std::unordered_set<P>& properties() const {
        return get<P>(m_properties);
    }

    void merge_with(const derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        assert(m_delineation.empty() && other.m_delineation.empty());
        merge(m_properties, other.m_properties);
        if (m_level > 0) {
            base_of(m_underlying)->merge_with(*base_of(other.m_underlying));
        }
    }
};

template<typename Properties>
class delineated_derivation_impl : delineated_derivation<Properties> {
    /*
    template<typename P>
    friend sampled_derivation<P>::ref make_sampled_derivation(delineated_derivation<P>::ref base, const ran& main_sample);
    */

    derivation<Properties>::ref m_base;
    delineation m_delineation;

    static assignment empty_assignment; // TODO put it in sampled assignment?

public:
    // should be private, but does not work with make_shared:
    delineated_derivation_impl(derivation<Properties>::ref base) : m_base(base) {
        assert(instance_of<sampled_derivation<Properties>::ref>(base));
    }

    derivation<Properties>::ref& base() { return m_base; };

    delineation& delin() { return m_delineation; };
    const assignment& underlying_sample() const {
        if(m_level == 0) { return empty_assignment; }
        else {
            return  static_cast<sampled_derivation<Properties>::ref>(underlying())->sample();
        }
    }

    derivation<Properties>::ref& underlying() { return m_base->underlying(); };
    poly_pool& polys() { return m_base->polys(); };
    projections& proj() { return m_base->proj(); };
    carl::Variable main_var() const { return m_base->main_var(); };
    size_t level() const { return m_base->level(); };
    template<typename P>
    void insert(P property) { m_base->insert(property); };
    template<typename P>
    bool contains(const P& property) const { return m_base->contains(property); };
    template<typename P>
    const std::unordered_set<P>& properties() const { return m_base->properties<P>(); };
    void merge_with(const derivation<Properties>& other) { m_base->merge_with(other) };
};

template<typename Properties>
class sampled_derivation_impl : sampled_derivation<Properties> {
    delineated_derivation<Properties>::ref m_delineated_base;
    std::optional<delineation_cell> m_cell;
    assignment m_sample;

public:
    // should be private, but does not work with make_shared
    sampled_derivation(delineated_derivation<Properties>::ref base, ran main_sample) : m_delineated_base(base) {
        m_sample = m_delineated_base->underlying_sample();
        m_sample.emplace(m_delineated_base->main_var(), main_sample);
    }

    delineated_derivation<Properties>::ref& delineated_base() { return m_delineated_base; };

    const delineation_cell& cell() { return *m_cell; }
    void delineate_cell() {
        m_cell = base()->delin().delineate_cell(m_sample.at(base()->main_var()));
    }

    const assignment& sample() const { return m_sample; };
    const ran& main_var_sample() const { return m_sample.at(base()->main_var()); };

    derivation<Properties>::ref& base() { return m_delineated_base->base(); };
    delineation& delin() { return m_delineated_base->delin(); };
    const assignment& underlying_sample() const { return m_delineated_base->underlying_sample(); }
    derivation<Properties>::ref& underlying() { return m_delineated_base->underlying(); };
    poly_pool& polys() { return m_delineated_base->polys(); };
    projections& proj() { return m_delineated_base->proj(); };
    carl::Variable main_var() const { return m_delineated_base->main_var(); };
    size_t level() const { return m_delineated_base->level(); };
    template<typename P>
    void insert(P property) { m_delineated_base->insert(property); };
    template<typename P>
    bool contains(const P& property) const { return m_delineated_base->contains(property); };
    template<typename P>
    const std::unordered_set<P>& properties() const { return m_delineated_base->properties<P>(); };
    void merge_with(const derivation<Properties>& other) { m_delineated_base->merge_with(other) };
};

template<typename Properties>
derivation<Properties>::ref make_derivation(projections& proj, const assignment& assignment, size_t level) {
    const auto& vars = proj.polys().var_order();

    auto current = std::make_shared<derivation_impl<Properties>>(proj, 0, derivation<Properties>::ref(nullptr));
    for (size_t i = 1; i <= level; i++) {
        auto base = std::make_shared<derivation_impl<Properties>>(proj, level, current);
        auto delineated_base = std::make_shared<delineated_derivation_impl<Properties>>(base);
        if (assignment.find(vars[level-1]) != assignment.end()) {
            current = std::make_shared<sampled_derivation<Properties>>(delineated_base, assignment.at(vars[level-1]));
        } else {
            current = delineated_base;
        }
    }

    return current;
}

template<typename Properties>
sampled_derivation<Properties>::ref make_sampled_derivation(delineated_derivation<Properties>::ref delineated_base, const ran& main_sample) {
    auto sampled_der = std::make_shared<sampled_derivation_impl<Properties>>(delineated_base, main_sample);
    sampled_der->delineate_cell();
    return sampled_der;
}

template<typename Properties>
void merge_underlying(std::vector<std::reference_wrapper<derivation<P>>>& derivations) {
    std::set<derivation_ref<Properties>> underlying;
    for (auto& deriv : derivations) {
        underlying.insert(deriv->underlying());
    }
    assert(!underlying.empty());
    auto first_underlying = *underlying.begin();
    for (auto iter = std::next(underlying.begin()); iter != underlying.end(); iter++) {
        first_underlying->merge_with(**iter);
    }
    for (auto& deriv : derivations) {
        deriv->m_underlying = first_underlying;
    }
}


}