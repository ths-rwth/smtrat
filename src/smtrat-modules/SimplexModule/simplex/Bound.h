#pragma once

namespace smtrat::simplex {

using Var = std::size_t; // TODO: unify with SimplexVariable?

enum class BoundType { LOWER, UPPER, EQUAL, NEQ };

template<typename Val>
struct Bound {
    Val       m_value;
    Var       m_var;
    BoundType m_type;
    FormulaT  m_origin;
    bool      m_is_derived = false;
    bool      m_is_active  = false;

    Bound(Var var, BoundType type, const Val& rhs, const FormulaT& origin)
    : m_value(rhs), m_var(var), m_type(type), m_origin(origin) {}
};

template<class Val>
std::ostream& operator<<(std::ostream& out, const Bound<Val>& bound) {
    out << "(" << "sv_" << bound.m_var;
    switch (bound.m_type) {
    case BoundType::LOWER: out << " >= "; break;
    case BoundType::UPPER: out << " <= "; break;
    case BoundType::EQUAL: out << " = ";  break;
    case BoundType::NEQ:   out << " != "; break;
    default: assert(false);
    }
    out << bound.m_value << ")";
	return out;
}

/**
 * Class for Bound storage. Storing all Bounds in the internal container m_data ensures locality.
 * Gives out handles in the form of Ref objects,
 * so that simplex only needs to store these handles in its various datastructures.
 * This could also be achieved by using references, (smart) pointers or iterators,
 * but I claim that this approach leads to more readable and less error-prone code.
 * Each bound is also associated to a Formula from which it originated.
 * 
 * TODO: add possibility for deleting bounds and reusing the storage. E.g.: use a reference counter
 * in BoundRef?
 */
template<typename Val>
class Bounds {
public:
    class Ref;
private:
    std::vector<Bound<Val>> m_data;
    std::map<FormulaT, Ref> m_origin_to_bound;

public:
    /// @brief wrapper around index into the internal container of Bounds
    class Ref {
    private:
        friend class Bounds;
        std::size_t m_value;
        explicit Ref(std::size_t id) : m_value(id) {}

    public:
        Ref(const Ref& other) = default;
        Ref& operator=(const Ref& other) = default;

        bool operator==(const Ref& other) const {
            return this->m_value == other.m_value;
        }
        bool operator!=(const Ref& other) const {
            return this->m_value != other.m_value;
        }

        struct cmp {
        private:
            const Bounds& m_comparison_data;
        public:
            bool operator() (const Ref& lhs, const Ref& rhs) const {
                return m_comparison_data[lhs].m_value <= m_comparison_data[rhs].m_value;
            }
            cmp(const Bounds& bs) : m_comparison_data(bs) {}
        };

        using Set = std::set<Ref, cmp>;
    };

    Bounds() : m_data(), m_origin_to_bound() {}

    /**
     * Inserts a new Bound into the storage and associates it with the given origin.
     * @return a Ref object containing the index of the new bound in m_data
     */
    Ref add(Var var, BoundType type, const Val& rhs, const FormulaT& origin) {
        Ref result(m_data.size());
        m_data.emplace_back(var, type, rhs, origin);
        m_origin_to_bound.emplace(origin, result); // TODO: what if the origin already exists?
        return result;
    }

    Ref add_derived(Var var, BoundType type, const Val& rhs, const FormulaT& origin) {
        Ref result = add(var, type, rhs, origin);
        m_data[result.m_value].m_is_derived = true;
        return result;
    }

    Bound<Val>& operator[](const Ref& id) {
        return m_data[id.m_value];
    }

    const Bound<Val>& operator[](const Ref& id) const {
        return m_data[id.m_value];
    }

    Ref get_from_origin(const FormulaT& origin) const {
        auto it = m_origin_to_bound.find(origin);
        assert(it != m_origin_to_bound.end());
        return it->second;
    }

    void reserve(std::size_t n) const {
        m_data.reserve(n);
    }
};

}