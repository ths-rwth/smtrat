namespace smtrat::cadcells::representation::approximation {

inline Rational mediant(Rational a, Rational b) {
    return Rational(a.get_num()+b.get_num(), a.get_den()+b.get_den());
}

inline Rational approximate_RAN(const RAN& r) {
    if (r.is_numeric()) return r.value();
    return carl::branching_point(r);
}

inline Rational approximate_RAN_sb(const RAN& r) {
    if (r.is_numeric()) return r.value();
    return carl::sample_stern_brocot(r.interval(), false);
}

inline Rational approximate_RAN_below(const RAN& r) {
    if (r.is_numeric()) return r.value();
    Rational res = carl::branching_point(r);
    while (res > r) {
        res = carl::sample_between(r.interval().lower(), res);
    }
    return res;
}

inline Rational approximate_RAN_above(const RAN& r) {
    if (r.is_numeric()) return r.value();
    Rational res = carl::branching_point(r);
    while (res < r) {
        res = carl::sample_between(res, r.interval().upper());
    }
    return res;
}

// inner is closer to the sample point
template<ApxRoot AR>
inline Rational approximate_root_above(const RAN& inner, const RAN& outer);
template<ApxRoot AR>
Rational approximate_root_below(const RAN& inner, const RAN& outer);

template<>
inline Rational approximate_root_above<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer) {
    return carl::sample_between(inner, outer);
}
template<>
inline Rational approximate_root_below<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer) {
    return carl::sample_between(outer, inner);
}

template<>
inline Rational approximate_root_above<ApxRoot::SIMPLE_REPRESENTATION>(const RAN& inner, const RAN& outer) {
    assert(inner < outer);
    Rational inner_simple, outer_simple;

    if (carl::is_integer(outer)) outer_simple = outer.value() - 1;
    else if (outer.is_numeric()) outer_simple = carl::floor(outer.value());
    else outer_simple = carl::floor(outer.interval().lower());
    // If an integer is between inner and outer, return the closest to outer
    if (outer_simple > inner) return outer_simple; // TODO: add option to choose another integer

    inner_simple = approximate_RAN_above(inner);
    outer_simple = approximate_RAN_below(outer);
    assert(inner_simple < outer_simple);
    RationalInterval region = RationalInterval(inner_simple, carl::BoundType::STRICT, outer_simple, carl::BoundType::STRICT);
    return carl::sample_stern_brocot(region, false);
}

template<>
inline Rational approximate_root_below<ApxRoot::SIMPLE_REPRESENTATION>(const RAN& inner, const RAN& outer) {
    assert(inner > outer);
    Rational inner_simple, outer_simple;

    if (carl::is_integer(outer)) outer_simple = outer.value() + 1;
    else if (outer.is_numeric()) outer_simple = carl::ceil(outer.value());
    else outer_simple = carl::ceil(outer.interval().upper());
    // If an integer is between inner and outer, return the closest to outer
    if (outer_simple < inner) return outer_simple; // TODO: add option to choose another integer

    inner_simple = approximate_RAN_below(inner);
    outer_simple = approximate_RAN_above(outer);

    assert(inner_simple > outer_simple);
    RationalInterval region = RationalInterval(outer_simple, carl::BoundType::STRICT, inner_simple, carl::BoundType::STRICT);
    return carl::sample_stern_brocot(region, false);
}

template<>
inline Rational approximate_root_above<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple, mid;
    
    if (inner.is_numeric()) inner_simple = carl::ceil(inner.value());
    else inner_simple = carl::ceil(inner.interval().upper());
    if (outer.is_numeric()) outer_simple = carl::ceil(outer.value());
    else outer_simple = carl::ceil(outer.interval().upper());

    // make sure inner_simple is below outer and outer_simple is the first integer > outer
    while (inner_simple >= outer) {
        if (inner_simple < outer_simple) outer_simple = inner_simple;
        inner_simple = inner_simple - 1;
    }

    for (std::size_t i = 0; i < apx_settings().n_sb_iterations;) {
        mid = mediant(inner_simple, outer_simple);
        if (mid >= outer) outer_simple = mid;
        else { // mid < outer
            inner_simple = mid;
            if (inner < mid) ++i;
        }
    }

    return mid;
}

template<>
inline Rational approximate_root_below<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple, mid;

    if (inner.is_numeric()) inner_simple = carl::floor(inner.value());
    else inner_simple = carl::floor(inner.interval().lower());
    if (outer.is_numeric()) outer_simple = carl::floor(outer.value());
    else outer_simple = carl::floor(outer.interval().lower());

    // make sure inner_simple is above outer and outer_simple is the first integer < outer
    while (inner_simple <= outer) {
        if (inner_simple > outer_simple) outer_simple = inner_simple;
        inner_simple = inner_simple + 1;
    }

    for (std::size_t i = 0; i < apx_settings().n_sb_iterations;) {
        mid = mediant(inner_simple, outer_simple);
        if (mid <= outer) outer_simple = mid;
        else { // mid > outer
            inner_simple = mid;
            if (inner > mid) ++i;
        }
    }

    return mid;
}

template<>
inline Rational approximate_root_above<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer) {
    Rational apx_outer = approximate_RAN_below(outer);
    Rational apx_inner = approximate_RAN_above(inner);
    Rational upper_bound = (apx_settings().root_ratio_upper * apx_outer) + ((1 - apx_settings().root_ratio_upper) * apx_inner);
    Rational lower_bound = (apx_settings().root_ratio_lower * apx_outer) + ((1 - apx_settings().root_ratio_lower) * apx_inner);
    RationalInterval region = RationalInterval(lower_bound, carl::BoundType::STRICT, upper_bound, carl::BoundType::STRICT);
    return carl::sample_stern_brocot(region, false);
}

template<>
inline Rational approximate_root_below<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer) {
    Rational apx_outer = approximate_RAN_above(outer);
    Rational apx_inner = approximate_RAN_below(inner);
    Rational lower_bound = (apx_settings().root_ratio_upper * apx_outer) + ((1 - apx_settings().root_ratio_upper) * apx_inner);
    Rational upper_bound = (apx_settings().root_ratio_lower * apx_outer) + ((1 - apx_settings().root_ratio_lower) * apx_inner);
    RationalInterval region = RationalInterval(lower_bound, carl::BoundType::STRICT, upper_bound, carl::BoundType::STRICT);
    return carl::sample_stern_brocot(region, false);
}

template<ApxRoot AR> 
inline Rational approximate_root(const RAN& inner, const RAN& outer, bool below) {
    return below ? approximate_root_below<AR>(inner, outer) : approximate_root_above<AR>(inner, outer);
}

}