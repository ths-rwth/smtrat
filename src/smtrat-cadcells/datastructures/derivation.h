#pragma once

#include "../common.h"

#include "delineation.h"
#include "polynomials.h"
#include "projections.h"
#include "properties.h"

namespace smtrat::cadcells::datastructures {

template<typename Properties>
class BaseDerivation;
template<typename Properties>
class DelineatedDerivation;
template<typename Properties>
class SampledDerivation;

template<typename Properties>
using BaseDerivationRef = std::shared_ptr<BaseDerivation<Properties>>;
template<typename Properties>
using DelineatedDerivationRef = std::shared_ptr<DelineatedDerivation<Properties>>;

template<typename Properties>
using SampledDerivationRef = std::shared_ptr<SampledDerivation<Properties>>;

/**
 * A reference to a derivation, which is either
 * - a @ref BaseDerivation (a set of properties for each level)
 * - a @ref DelineatedDerivation (a @ref BaseDerivation with an underlying @ref SampledDerivation on which the properties can be delineated)
 * - a @ref SampledDerivation (a @ref DelineatedDerivation with an underlying @ref SampledDerivation plus a sample on the current level such that a delineated interval can be computed)
 * 
 * ## Memory management
 * 
 * Memory management is based on std::shared_ptr. A SampledDerivation holds a shared pointer to a DelineatedDerivation, which in turn holds a shared pointer to BaseDerivation. The BaseDerivation holds a @ref DerivationRef to the underlying derivation. Note that not all combinations are legal; i.e. the underlying derivation of a delineated derivation must be a sampled derivation.
 */
template<typename Properties>
class DerivationRef {
    std::variant<BaseDerivationRef<Properties>, DelineatedDerivationRef<Properties>, SampledDerivationRef<Properties>> m_data;

public:
    DerivationRef(const BaseDerivationRef<Properties>& data)
        : m_data(data) {}
    DerivationRef(const DelineatedDerivationRef<Properties>& data)
        : m_data(data) {}
    DerivationRef(const SampledDerivationRef<Properties>& data)
        : m_data(data) {}

    bool is_null() const {
        if (std::holds_alternative<BaseDerivationRef<Properties>>(m_data)) {
            return std::get<BaseDerivationRef<Properties>>(m_data) == nullptr;
        } else if (std::holds_alternative<DelineatedDerivationRef<Properties>>(m_data)) {
            return std::get<DelineatedDerivationRef<Properties>>(m_data) == nullptr;
        } else {
            return std::get<SampledDerivationRef<Properties>>(m_data) == nullptr;
        }
    }
    bool is_sampled() const {
        return std::holds_alternative<SampledDerivationRef<Properties>>(m_data);
    }

    auto& base_ref() {
        if (std::holds_alternative<BaseDerivationRef<Properties>>(m_data)) {
            return std::get<BaseDerivationRef<Properties>>(m_data);
        } else if (std::holds_alternative<DelineatedDerivationRef<Properties>>(m_data)) {
            return std::get<DelineatedDerivationRef<Properties>>(m_data)->base();
        } else {
            assert(is_sampled());
            return std::get<SampledDerivationRef<Properties>>(m_data)->base();
        }
    }
    auto& delineated_ref() {
        if (std::holds_alternative<DelineatedDerivationRef<Properties>>(m_data)) {
            return std::get<DelineatedDerivationRef<Properties>>(m_data);
        } else {
            assert(is_sampled());
            return std::get<SampledDerivationRef<Properties>>(m_data)->delineated();
        }
    }
    auto& sampled_ref() {
        assert(is_sampled());
        return std::get<SampledDerivationRef<Properties>>(m_data);
    }

    const auto& base_ref() const {
        if (std::holds_alternative<BaseDerivationRef<Properties>>(m_data)) {
            return std::get<BaseDerivationRef<Properties>>(m_data);
        } else if (std::holds_alternative<DelineatedDerivationRef<Properties>>(m_data)) {
            return std::get<DelineatedDerivationRef<Properties>>(m_data)->base();
        } else {
            assert(is_sampled());
            return std::get<SampledDerivationRef<Properties>>(m_data)->base();
        }
    }
    const auto& delineated_ref() const {
        if (std::holds_alternative<DelineatedDerivationRef<Properties>>(m_data)) {
            return std::get<DelineatedDerivationRef<Properties>>(m_data);
        } else {
            assert(is_sampled());
            return std::get<SampledDerivationRef<Properties>>(m_data)->delineated();
        }
    }
    const auto& sampled_ref() const {
        assert(is_sampled());
        return std::get<SampledDerivationRef<Properties>>(m_data);
    }

    auto& base() {
        return *base_ref();
    }
    auto& delineated() {
        return *delineated_ref();
    }
    auto& sampled() {
        return *sampled_ref();
    }
    const auto& base() const {
        return *base_ref();
    }
    const auto& delineated() const {
        return *delineated_ref();
    }
    const auto& sampled() const {
        return *sampled_ref();
    }

    template<typename P>
    friend bool operator==(const DerivationRef<P>& lhs, const DerivationRef<P>& rhs) {
        return lhs.m_data == rhs.m_data;
    }
    template<typename P>
    friend bool operator<(const DerivationRef<P>& lhs, const DerivationRef<P>& rhs) {
        return lhs.m_data < rhs.m_data;
    }
};

/**
 * A BaseDerivation has a level and a set of properties of this level, and an underlying derivation representing the lower levels.
 *  
 * @tparam Properties Set of properties (from the operator)
 */
template<typename Properties>
class BaseDerivation {
    template<typename P>
    friend void merge_underlying(std::vector<SampledDerivationRef<P>>& derivations);

    DerivationRef<Properties> m_underlying;
    Projections& m_projections;

    size_t m_level;
    Properties m_properties;

public:
    // should be private, but does not work with make_shared:
    BaseDerivation(Projections& Projections, DerivationRef<Properties> underlying, size_t level) : m_underlying(underlying), m_projections(Projections), m_level(level) {
        assert((level == 0 && m_underlying.is_null()) || (level > 0 && !m_underlying.is_null()));
    }

    DerivationRef<Properties>& underlying() { return m_underlying; }
    DerivationRef<Properties>& underlying() const { return m_underlying; }

    PolyPool& polys() { return m_projections.polys(); }
    Projections& proj() { return m_projections; }
    carl::Variable main_var() const {
        if (m_level == 0) return carl::Variable::NO_VARIABLE;
        else return m_projections.polys().var_order()[m_level-1];
    }
    size_t level() const { return m_level; }

    template<typename P>
    void insert(P property) {
        assert(property.level() <= m_level && property.level() >= 0);

        if (property.level() == m_level) {
            prop_insert<P>(m_properties, property);
        } else {
            assert(!m_underlying.is_null());
            m_underlying.base().insert(property);
        }
    }

    template<typename P>
    bool contains(const P& property) const {
        assert(property.level() <= m_level && property.level() >= 0);

        if (property.level() == m_level) {
            return prop_has<P>(m_properties, property);
        } else {
            assert(!m_underlying.is_null());
            return m_underlying.base().contains(property);
        }
    }
    template<typename P>
    const PropertiesTSet<P>& properties() const {
        return prop_get<P>(m_properties);
    }

    void merge_with(const BaseDerivation<Properties>& other) {
        assert(other.m_level == m_level && &other.m_projections == &m_projections);
        merge(m_properties, other.m_properties);
        if (m_level > 0) {
            m_underlying.base().merge_with(other.m_underlying.base());
        }
    }
};

/**
 * A DelineatedDerivation is a BaseDerivation with a Delineation and an underlying SampledDerivation.
 * 
 * @tparam Properties Set of properties
 */
template<typename Properties>
class DelineatedDerivation {
    BaseDerivationRef<Properties> m_base;
    Delineation m_delineation;

public:
    // should be private, but does not work with make_shared:
    DelineatedDerivation(BaseDerivationRef<Properties> base)
        : m_base(base) {
        assert(base->level() == 0 || base->underlying().is_sampled());
    }

    BaseDerivationRef<Properties>& base() {
        return m_base;
    };
    BaseDerivationRef<Properties>& base() const {
        return m_base;
    };

    Delineation& delin() {
        return m_delineation;
    };
    const Assignment& underlying_sample() const {
        if (m_base->level() <= 1) {
            return empty_assignment;
        } else {
            return underlying().sampled().sample();
        }
    }

    DerivationRef<Properties>& underlying() {
        return m_base->underlying();
    };
    DerivationRef<Properties>& underlying() const {
        return m_base->underlying();
    };
    PolyPool& polys() {
        return m_base->polys();
    };
    Projections& proj() {
        return m_base->proj();
    };
    carl::Variable main_var() const {
        return m_base->main_var();
    };
    size_t level() const {
        return m_base->level();
    };
    template<typename P>
    void insert(P property) {
        m_base->insert(property);
    };
    template<typename P>
    bool contains(const P& property) const {
        return m_base->contains(property);
    };
    template<typename P>
    const PropertiesTSet<P>& properties() const {
        return m_base->template properties<P>();
    };

    void merge_with(const DelineatedDerivation<Properties>& other) {
        assert(m_delineation.empty() && other.m_delineation.empty());
        m_base->merge_with(*other.m_base);
    };
};

/**
 * A SampledDerivation is a DelineatedDerivation with a sample and an DelineationInterval w.r.t. to this sample.
 * 
 * @tparam Properties Set of properties
 */
template<typename Properties>
class SampledDerivation {
    DelineatedDerivationRef<Properties> m_delineated;
    std::optional<DelineationInterval> m_cell;
    Assignment m_sample;

public:

    // should be private, but does not work with make_shared
    SampledDerivation(DelineatedDerivationRef<Properties> base, RAN main_sample) : m_delineated(base) {
        m_sample = m_delineated->underlying_sample();
        if (m_delineated->level() > 0) {
            m_sample.emplace(m_delineated->main_var(), main_sample);
        }
    }

    DelineatedDerivationRef<Properties>& delineated() { return m_delineated; };
    DelineatedDerivationRef<Properties>& delineated() const { return m_delineated; };

    const DelineationInterval& cell() const { return *m_cell; }
    /**
     * Determines the cell w.r.t. the delineation.
     * 
     */
    void delineate_cell() {
        if (m_delineated->level() > 0) {
            m_cell = m_delineated->delin().delineate_cell(main_var_sample());
        }
    }

    void setEndpoints(bool l_flag, bool u_flag) {
        if(l_flag) {
            m_cell.value().set_lower_inclusive();
        }
        if(u_flag) {
            m_cell.value().set_upper_inclusive();
        }
    }

    void set_strictness_of_ancestor_intervals() {
        m_cell.value().set_strictness_of_ancestor_intervals();
    }

    const Assignment& sample() const { return m_sample; };
    const RAN& main_var_sample() const { return m_sample.at(m_delineated->main_var()); };

    BaseDerivationRef<Properties>& base() { return m_delineated->base(); };
    BaseDerivationRef<Properties>& base() const { return m_delineated->base(); };
    Delineation& delin() { return m_delineated->delin(); };
    const Assignment& underlying_sample() const { return m_delineated->underlying_sample(); }
    DerivationRef<Properties>& underlying() { return m_delineated->underlying(); };
    PolyPool& polys() { return m_delineated->polys(); };
    Projections& proj() { return m_delineated->proj(); };
    carl::Variable main_var() const { return m_delineated->main_var(); };
    size_t level() const { return m_delineated->level(); };
    template<typename P>
    void insert(P property) { m_delineated->insert(property); };
    template<typename P>
    bool contains(const P& property) const { return m_delineated->contains(property); };
    template<typename P>
    const PropertiesTSet<P>& properties() const { return m_delineated->template properties<P>(); };

    void merge_with(const SampledDerivation<Properties>& other) {
        assert(!m_cell && other.m_cell);
        m_delineated->merge_with(other);
    };
};

/**
 * Initializes a derivation according the the given assignment and level.
 */
template<typename Properties>
DerivationRef<Properties> make_derivation(Projections& proj, const Assignment& assignment, size_t level) {
    const auto& vars = proj.polys().var_order();

    auto zero_base = std::make_shared<BaseDerivation<Properties>>(proj, BaseDerivationRef<Properties>(nullptr), 0);
    auto zero_delineated = std::make_shared<DelineatedDerivation<Properties>>(zero_base);
    DerivationRef<Properties> current = std::make_shared<SampledDerivation<Properties>>(zero_delineated, RAN(0));

    for (size_t i = 1; i <= level; i++) {
        auto base = std::make_shared<BaseDerivation<Properties>>(proj, current, i);
        auto delineated = std::make_shared<DelineatedDerivation<Properties>>(base);
        if (assignment.find(vars[i - 1]) != assignment.end()) {
            current = std::make_shared<SampledDerivation<Properties>>(delineated, assignment.at(vars[i - 1]));
        } else {
            current = delineated;
        }
    }

    return current;
}

/**
 * Initializes a sampled derivation w.r.t. the delineated derivation and sample.
 */
template<typename Properties>
SampledDerivationRef<Properties> make_sampled_derivation(DelineatedDerivationRef<Properties> delineated, const RAN& main_sample) {
    auto sampled_der = std::make_shared<SampledDerivation<Properties>>(delineated, main_sample);
    sampled_der->delineate_cell();
    return sampled_der;
}

/**
 * Merges the underlying derivations of a set of sampled derivations. After the operation, all sampled derivations point to the same underlying derivation.
 */
template<typename Properties>
void merge_underlying(std::vector<SampledDerivationRef<Properties>>& derivations) {
    std::set<DerivationRef<Properties>> underlying;
    for (auto& deriv : derivations) {
        underlying.insert(deriv->underlying());
    }
    assert(!underlying.empty());
    auto first_underlying = *underlying.begin();
    for (auto iter = std::next(underlying.begin()); iter != underlying.end(); iter++) {
        first_underlying.base().merge_with(iter->base());
    }
    for (auto& deriv : derivations) {
        deriv->base()->m_underlying = first_underlying;
    }
}


} // namespace smtrat::cadcells::datastructures