namespace smtrat::cadcells::representation::approximation {

struct RANApxSettings {
    static constexpr std::size_t n_sb_iterations = 2;
    static constexpr double root_ratio_upper = 0.875;
    static constexpr double root_ratio_lower = 0.75;
};

Rational mediant(Rational a, Rational b) {
    return Rational(a.get_num()+b.get_num(), a.get_den()+b.get_den());
}

Rational approximate_RAN(const RAN& r) {
    if (r.is_numeric()) return r.value();
    return carl::branching_point(r);
}

Rational approximate_RAN_below(const RAN& r) {
    if (r.is_numeric()) return r.value();
    Rational res = carl::branching_point(r);
    while (res > r) {
        res = carl::sample_between(r.interval().lower(), res);
    }
    return res;
}

Rational approximate_RAN_above(const RAN& r) {
    if (r.is_numeric()) return r.value();
    Rational res = carl::branching_point(r);
    while (res < r) {
        res = carl::sample_between(res, r.interval().upper());
    }
    return res;
}

enum ApxRoot {SAMPLE_MID, SIMPLE_REPRESENTATION, STERN_BROCOT, FIXED_RATIO, MAXIMIZE};
// inner is closer to the sample point
template<ApxRoot AR>
Rational approximate_root_above(const RAN& inner, const RAN& outer);
template<ApxRoot AR>
Rational approximate_root_below(const RAN& inner, const RAN& outer);

template<>
Rational approximate_root_above<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer) {
    return carl::sample_between(inner, outer);
}
template<>
Rational approximate_root_below<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer) {
    return carl::sample_between(outer, inner);
}

template<>
Rational approximate_root_above<ApxRoot::SIMPLE_REPRESENTATION>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple;

    if (inner.is_integral()) inner_simple = inner.value();
    else inner_simple = carl::ceil(inner.interval().upper());
    if (outer.is_integral()) outer_simple = outer.value();
    else outer_simple = carl::floor(outer.interval().lower());
    // if there is an integer between the points, return the closest to outer
    if (outer_simple > inner_simple) return outer_simple;
    if (outer_simple > inner) return outer_simple;
    // Otherwise: inner_simple < outer < inner < outer_simple (or reversed)
    // apply stern-brocot until a sample between the two points is found
    if (inner_simple == outer_simple) inner_simple = outer_simple + Rational(1);

    while(true) {
        Rational mid = mediant(inner_simple, outer_simple);
        if (mid <= inner) outer_simple = mid;
        else if (mid >= outer) inner_simple = mid;
        else return mid;
    }
    assert(false); // unreachable
    return carl::sample_between(inner, outer);
}

template<>
Rational approximate_root_below<ApxRoot::SIMPLE_REPRESENTATION>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple;

    if (inner.is_integral()) inner_simple = inner.value();
    else inner_simple = carl::floor(inner.interval().lower());
    if (outer.is_integral()) outer_simple = outer.value();
    else outer_simple = carl::ceil(outer.interval().upper());
    // if there is an integer between the points, return the closest to outer
    if (outer_simple < inner_simple) return outer_simple;
    if (outer_simple < inner) return outer_simple;
    // Otherwise: inner_simple < outer < inner < outer_simple (or reversed)
    // apply stern-brocot until a sample between the two points is found
    if (inner_simple == outer_simple) inner_simple = outer_simple - Rational(1);

    while(true) {
        Rational mid = mediant(inner_simple, outer_simple);
        if (mid >= inner) outer_simple = mid;
        else if (mid <= outer) inner_simple = mid;
        else return mid;
    }
    assert(false); // unreachable
    return carl::sample_between(outer, inner);
}

template<>
Rational approximate_root_above<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple, mid;
    
    if (inner.is_numeric()) inner_simple = carl::ceil(inner.value());
    else inner_simple = carl::ceil(inner.interval().upper());
    if (outer.is_numeric()) outer_simple = carl::ceil(outer.value());
    else outer_simple = carl::ceil(outer.interval().upper());

    while (inner_simple >= outer) {
        if (inner_simple < outer_simple) outer_simple = inner_simple;
        inner_simple = inner_simple - 1;
    }

    for (std::size_t i = 0; i < RANApxSettings::n_sb_iterations;) {
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
Rational approximate_root_below<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer) {
    Rational inner_simple, outer_simple, mid;

    if (inner.is_numeric()) inner_simple = carl::floor(inner.value());
    else inner_simple = carl::floor(inner.interval().lower());
    if (outer.is_numeric()) outer_simple = carl::floor(outer.value());
    else outer_simple = carl::floor(outer.interval().lower());

    while (inner_simple <= outer) {
        if (inner_simple > outer_simple) outer_simple = inner_simple;
        inner_simple = inner_simple + 1;
    }

    for (std::size_t i = 0; i < RANApxSettings::n_sb_iterations;) {
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
Rational approximate_root_above<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer) {
    Rational apx_outer = approximate_RAN_below(outer);
    Rational apx_inner = approximate_RAN(inner);
    Rational upper_bound = (RANApxSettings::root_ratio_upper * apx_outer) + ((1 - RANApxSettings::root_ratio_upper) * apx_inner);
    Rational lower_bound = (RANApxSettings::root_ratio_lower * apx_outer) + ((1 - RANApxSettings::root_ratio_lower) * apx_inner);
    RationalInterval region = RationalInterval(lower_bound, upper_bound);
    Rational res = carl::sample_stern_brocot(region, false);
    return carl::sample_stern_brocot(region, false);
}

template<>
Rational approximate_root_below<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer) {
    Rational apx_outer = approximate_RAN_above(outer);
    Rational apx_inner = approximate_RAN(inner);
    Rational lower_bound = (RANApxSettings::root_ratio_upper * apx_outer) + ((1 - RANApxSettings::root_ratio_upper) * apx_inner);
    Rational upper_bound = (RANApxSettings::root_ratio_lower * apx_outer) + ((1 - RANApxSettings::root_ratio_lower) * apx_inner);
    RationalInterval region = RationalInterval(lower_bound, upper_bound);
    Rational res = carl::sample_stern_brocot(region, false);
    return carl::sample_stern_brocot(region, false);
}

template<ApxRoot AR> 
Rational approximate_root(const RAN& inner, const RAN& outer, bool below) {
    return below ? approximate_root_below<AR>(inner, outer) : approximate_root_above<AR>(inner, outer);
}

}