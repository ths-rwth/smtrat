#pragma once

#include "../common.h"

#include "polynomials.h"
#include "properties.h"

namespace smtrat::cadcells::datastructures {

template<typename Properties>
std::variant<std::shared_ptr<Properties>, std::shared_ptr<cell_derivation<Properties>>> make_derivation(projections& projections, const assignment& assignment) {
//TODO
}

std::shared_ptr<cell_derivation<Properties>> make_cell_derivation(std::shared_ptr<derivation<Properties>> delineation, const ran& main_sample) {
    assert(std::holds_alternative<std::shared_ptr<cell_derivation<Properties>>>(delineation->m_underlying));
    auto cell_del = cell_derivation(delineation);
    cell_del.set_sample(main_sample);
    return cell_del;
}

template<typename Properties>
class derivation {
    projections& m_projections;

    size_t m_level;
    Properties m_properties;
    delineation m_delineation;

    std::optional<std::variant<std::shared_ptr<derivation<Properties>>, std::shared_ptr<cell_derivation<Properties>>>> m_underlying; 

    derivation(const projections& projections, size_t level, std::shared_ptr<derivation> underlying) : m_projections(projections), m_level(level), m_underlying(underlying) {}

    friend std::variant<std::shared_ptr<derivation<Properties>>, std::shared_ptr<cell_derivation<Properties>>> make_derivation(projections& projections, const assignment& assignment);

public:

    auto& poly_pool() { return m_projections.poly_pool(); }
    auto& proj() { return m_projections; }
    auto main_var() { return poly_pool().var_order()[m_level-1]; }
    size_t level() { return m_level; }

    // TODO consider lowest level:
    auto underlying() { return *m_underlying; }
    auto underlying_cell() { return std::get<std::shared_ptr<cell_derivation<Ts...>>>(*m_underlying); }
    assignment& underlying_sample() { return underlying_cell()->sample(); }

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

private:
    void merge(const derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        assert(m_delineation.empty() && other.m_delineation.empty());
        merge(m_properties, other.m_properties);
        merge_underlying_cell(other);
    }

public:
    void merge_underlying_cell(const derivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        if (m_level > 0) {
            assert(m_lower != std::nullptr_t && other.m_lower != std::nullptr_t);
            // TODO resolve variant
            m_lower.merge(*other.m_lower);
            other.m_lower = m_lower;
        }
    }
};

template<typename Properties>
class cell_derivation {
    std::shared_ptr<derivation<Properties>> m_base_derivation;
    std::optional<delineation_cell> m_delineation_cell;
    std::optional<assignment> m_sample;

    cell_derivation(std::shared_ptr<derivation<Properties>> base_derivation) : m_base_derivation(projections) {}

    friend std::variant<std::shared_ptr<derivation<Properties>>, std::shared_ptr<cell_derivation<Properties>>> make_derivation(projections& projections, const assignment& assignment);
    friend class derivation<Properties>;

public:
    auto& proj() { return m_base_derivation.proj(); }
    auto& base_derivation() { return m_base_derivation; }
    const delineation_cell& delineation_cell() { return m_delineation_cell; }

    void set_sample(const ran& main_sample) {
        m_delineation_cell = base_derivation().delineation().delineate_cell(main_sample);
        m_sample = base_derivation().underlying_sample();
        m_sample->insert(base_derivation().main_var(), main_sample);
    }

    const assignment& sample() {
        return m_sample;
    }
};

}