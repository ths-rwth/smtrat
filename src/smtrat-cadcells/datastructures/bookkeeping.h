#pragma once

#include "../common.h"
#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>

namespace smtrat::cadcells::datastructures {

class properties {
    const var_order& m_var_order;
    size_t m_level;
    std::shared_ptr<properties> m_lower; 
    std::set<property> m_properties;

private:
    void insert_at_level(size_t level, property&& property) {
        assert(level <= m_level);
        if (level < m_level) {
            assert(level > 0);
            assert(m_lower != std::nullptr);
            m_lower->insert_at_level(level, std::move(property));
        } else {
            m_properties.emplace(std::move(property));
        }
    }

public:
    properties(const var_order& order, size_t level) : m_var_order(order), m_level(level) {
        if (level > 0) {
            m_lower = std::make_shared<properties>(order, level-1);
        }
    }
    properties(const var_order& order, size_t level, std::shared_ptr<properties> lower) : properties(order, level), m_lower(lower) {}

    void insert(property&& property) {
        insert_at_level(property.compute_level(m_var_order), std::move(property));
    }

    void merge(const properties& other) {
        assert(other.m_level == m_level && other.m_var_order = m_var_order);
        m_properties.insert(other.m_properties.begin(), other.m_properties.end());
        if (level > 0) {
            assert(m_lower != std::nullptr_t && other.m_lower != std::nullptr_t);
            m_lower->merge(*other.m_lower);
        }
    }

    void merge_lower(properties& other) {
        assert(other.m_level == m_level && other.m_var_order = m_var_order);
        if (m_level > 0) {
            assert(m_lower != std::nullptr_t && other.m_lower != std::nullptr_t);
            m_lower.merge(*other.m_lower);
            other.m_lower = m_lower;
        }
    }
};
