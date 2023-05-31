#pragma once

#include "DeltaValue.h"

namespace smtrat::simplex {
template<class Number>
DeltaValue<Number>::DeltaValue()
    : m_real(0),
      m_delta(0) {}

template<class Number>
DeltaValue<Number>::DeltaValue(const Number& num)
    : m_real(num),
      m_delta(0) {}

template<class Number>
DeltaValue<Number>::DeltaValue(const Number& real, const Number& delta)
    : m_real(real),
      m_delta(delta) {}

template<class Number>
DeltaValue<Number>::DeltaValue(const DeltaValue<Number>& to_copy)
    : m_real(to_copy.real()),
      m_delta(to_copy.delta()) {}

template<class Number>
DeltaValue<Number>::~DeltaValue() {}

template<class Number>
DeltaValue<Number>& DeltaValue<Number>::operator=(const DeltaValue<Number>& value) {
    m_real = value.real();
    m_delta = value.delta();
    return *this;
}

template<class Number>
DeltaValue<Number> DeltaValue<Number>::operator+(const DeltaValue<Number>& value) const {
    Number num1 = m_real + value.real();
    Number num2 = m_delta + value.delta();
    return DeltaValue(num1, num2);
}

template<class Number>
void DeltaValue<Number>::operator+=(const DeltaValue<Number>& value) {
    m_real += value.real();
    m_delta += value.delta();
}

template<class Number>
DeltaValue<Number> DeltaValue<Number>::operator-(const DeltaValue<Number>& value) const {
    Number num1 = m_real - value.real();
    Number num2 = m_delta - value.delta();
    return DeltaValue(num1, num2);
}

template<class Number>
void DeltaValue<Number>::operator-=(const DeltaValue<Number>& value) {
    m_real -= value.real();
    m_delta -= value.delta();
}

template<class Number>
DeltaValue<Number> DeltaValue<Number>::operator*(const Number& a) const {
    Number num1 = a * m_real;
    Number num2 = a * m_delta;
    return DeltaValue(num1, num2);
}

template<class Number>
DeltaValue<Number> DeltaValue<Number>::operator*(const DeltaValue<Number>& value) const {
    Number num1 = value.real() * m_real;
    Number num2 = value.delta() * m_delta;
    return DeltaValue(num1, num2);
}

template<class Number>
void DeltaValue<Number>::operator*=(const DeltaValue<Number>& value) {
    m_real *= value.real();
    m_delta *= value.delta();
}

template<class Number>
void DeltaValue<Number>::operator*=(const Number& a) {
    m_real *= a;
    m_delta *= a;
}

template<class Number>
DeltaValue<Number> DeltaValue<Number>::operator/(const Number& a) const {
    Number num1 = Number(m_real) / a;
    Number num2 = Number(m_delta) / a;
    return DeltaValue(num1, num2);
}

template<class Number>
void DeltaValue<Number>::operator/=(const Number& a) {
    m_real /= a;
    m_delta /= a;
}

template<class Number>
bool DeltaValue<Number>::operator<(const DeltaValue<Number>& value) const {
    return (m_real < value.real()) || ((m_real == value.real()) && (m_delta < value.delta()));
}

template<class Number>
bool DeltaValue<Number>::operator<=(const DeltaValue<Number>& value) const {
    return (m_real < value.real()) || ((m_real == value.real()) && (m_delta <= value.delta()));
}

template<class Number>
bool DeltaValue<Number>::operator==(const DeltaValue<Number>& value) const {
    return (m_real == value.real()) && (m_delta == value.delta());
}

template<class Number>
bool DeltaValue<Number>::operator==(const Number& a) const {
    return (m_real == a) && (m_delta == 0);
}

template<class Number>
bool DeltaValue<Number>::operator<(const Number& a) const {
    return (m_real < a) || ((m_real == a) && (m_delta < 0));
}

template<class Number>
bool DeltaValue<Number>::operator>(const Number& a) const {
    return (m_real > a) || ((m_real == a) && (m_delta > 0));
}

template<class Number>
bool DeltaValue<Number>::operator<=(const Number& a) const {
    return (m_real < a || (m_real == a && m_delta <= 0));
}

template<class Number>
bool DeltaValue<Number>::operator>=(const Number& a) const {
    return (m_real > a || (m_real == a && m_delta >= 0));
}

template<class Number>
std::ostream& operator<<(std::ostream& out, const DeltaValue<Number>& value) {
    return out << value.real() << "+d*" << value.delta();
}

} // namespace smtrat::lra
