#pragma once

#include <cassert>
#include <sstream>
#include <cstring>

namespace smtrat::simplex {

/**
 * A class for Numbers enriched with an infinitesimal constant delta
 * This yields a new number type with elements of the form a + b*delta, where a,b are of
 * the underlying Number type.
 */
template<class Number>
class DeltaValue {
private:
    Number m_real;
    Number m_delta;

public:
    DeltaValue();
    DeltaValue(const Number& num);
    DeltaValue(const Number& real, const Number& delta);
    DeltaValue(const DeltaValue<Number>& to_copy);
    virtual ~DeltaValue();

    const Number& real () const { return m_real;  }
    const Number& delta() const { return m_delta; }

    DeltaValue<Number>& operator=  (const DeltaValue<Number>& value);

    DeltaValue<Number>  operator+  (const DeltaValue<Number>& value) const;
    void                operator+= (const DeltaValue<Number>& value);

    DeltaValue<Number>  operator-  (const DeltaValue<Number>& value) const;
    void                operator-= (const DeltaValue<Number>& value);

    DeltaValue<Number>  operator*  (const Number& a) const;
    void                operator*= (const Number& a);

    DeltaValue<Number>  operator*  (const DeltaValue<Number>& value) const;
    void                operator*= (const DeltaValue<Number>& value);

    DeltaValue<Number>  operator/  (const Number& a) const;
    void                operator/= (const Number& a);


    bool           operator<  (const DeltaValue<Number>& value) const;
    bool           operator>  (const DeltaValue<Number>& value) const {  return value < *this; }

    bool           operator<= (const DeltaValue<Number>& value) const;
    bool           operator>= (const DeltaValue<Number>& value) const { return value <= *this; }

    bool           operator== (const DeltaValue<Number>& value) const;
    bool           operator!= (const DeltaValue<Number>& value) const { return !(*this == value); }

    bool           operator== (const Number& a) const;
    bool           operator!= (const Number& a) const { return !(*this == a); }

    bool           operator<  (const Number& a) const;
    bool           operator>  (const Number& a) const;

    bool           operator<= (const Number& a) const;
    bool           operator>= (const Number& a) const;
};

template<typename Number>
std::ostream& operator<<(std::ostream& out, const DeltaValue<Number>& value);

template<typename Number>
DeltaValue<Number> abs(const DeltaValue<Number>& value) {
    if (value < Number(0)) return value * Number(-1);
    return value;
}

template<typename Number>
bool is_zero(const DeltaValue<Number>& value) {
    return value.real() == Number(0) && value.delta() == Number(0);
}

} // namespace smtrat::simplex

#include "DeltaValue.tpp"