namespace smtrat::cadcells::representation::approximation {

Rational mediant(Rational a, Rational b) {
    return Rational(a.get_num()+b.get_num(), a.get_den()+b.get_den());
}

Rational approximate_RAN(const RAN& r) {
    if (r.is_numeric()) return r.value();
    return carl::branching_point(r);
}

/*Rational approximate_RAN_below(const RAN& r, Rational lb) { // TODO: make this good
    Rational mid = carl::branching_point(r);
    if (mid < r) return mid;
    Rational floored = carl::floor(r);
    Rational res;
    while (floored < r) {
        res = floored;
        floored = mediant(floored, mid);
    }
    return res;
}

Rational approximate_RAN_above(const RAN& r, Rational ub) { // TODO: make this good
    Rational mid = carl::branching_point(r);
    if (mid > r) return mid;
    Rational ceiled = carl::ceil(r);
    Rational res;
    while (ceiled > r) {
        res = ceiled;
        ceiled = mediant(mid, ceiled);
    }
    return res;
}*/

enum ApxRoot {SAMPLE_MID, STERN_BROCOT, FIXED_RATIO, MAXIMIZE};
// inner is closer to the sample point
template<ApxRoot AR>
Rational approximate_root(const RAN& inner, const RAN& outer, bool below);

template<>
Rational approximate_root<ApxRoot::SAMPLE_MID>(const RAN& inner, const RAN& outer, bool below) {
    return below ? carl::sample_between(outer, inner) : carl::sample_between(inner, outer);
}

/*template<>
Rational approximate_root<ApxRoot::STERN_BROCOT>(const RAN& inner, const RAN& outer, bool below) {
    Rational apx_inner = carl::branching_point(inner); // TODO: this could be on the wrong side of the ran
    while(below ? (apx_inner < outer) : (apx_inner > outer)) {
        inner.refine();
        apx_inner = carl::branching_point(inner);
    }
    Rational apx_outer = carl::branching_point(outer);
    // TODO: find smaller representations for apx_inner and apx_outer
    Rational result = apx_inner;
    for (std::size_t i = 0; i < ApxSettings::n_sb_iterations; i++)
        result = mediant(result, apx_outer);
    return result;
}

template<>
Rational approximate_root<ApxRoot::FIXED_RATIO>(const RAN& inner, const RAN& outer, bool below) {
    Rational apx_inner = carl::branching_point(inner); // TODO: this could be on the wrong side of the ran
    while(below ? (apx_inner < outer) : (apx_inner > outer)) {
        inner.refine();
        apx_inner = carl::branching_point(inner);
    }
    Rational apx_outer = carl::branching_point(outer);
    // TODO: find smaller representations for apx_inner and apx_outer
    return (ApxSettings::root_ratio * apx_outer) + ((1 - ApxSettings::root_ratio) * apx_inner); // can lead to ugly large numbers in the rational description
}*/
}