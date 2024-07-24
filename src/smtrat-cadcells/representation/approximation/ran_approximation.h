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


struct sample_mid {
    static Rational below(const RAN& inner, const RAN& outer) {
        return carl::sample_between(inner, outer);
    }

    static Rational above(const RAN& inner, const RAN& outer) {
        return carl::sample_between(outer, inner);
    }
};


struct sample_simple_representation {
    static Rational below(const RAN& inner, const RAN& outer) {
        assert(inner < outer);
        Rational inner_simple, outer_simple;

        if (carl::is_integer(outer)) outer_simple = outer.value() - 1;
        else if (outer.is_numeric()) outer_simple = carl::floor(outer.value());
        else outer_simple = carl::floor(outer.interval().lower());
        // If an integer is between l and outer, return the closest to outer
        if (outer_simple > inner) return outer_simple; // TODO: add option to choose another integer

        inner_simple = approximate_RAN_above(inner);
        outer_simple = approximate_RAN_below(outer);
        assert(inner_simple < outer_simple);
        RationalInterval region(inner_simple, carl::BoundType::STRICT, outer_simple, carl::BoundType::STRICT);
        return carl::sample_stern_brocot(region, false);
    }

    static Rational above(const RAN& inner, const RAN& outer) {
        assert(inner > outer);
        Rational inner_simple, outer_simple;

        if (carl::is_integer(outer)) outer_simple = outer.value() + 1;
        else if (outer.is_numeric()) outer_simple = carl::ceil(outer.value());
        else outer_simple = carl::ceil(outer.interval().upper());
        // If an integer is between l and outer, return the closest to outer
        if (outer_simple < inner) return outer_simple; // TODO: add option to choose another integer

        inner_simple = approximate_RAN_below(inner);
        outer_simple = approximate_RAN_above(outer);
        assert(inner_simple > outer_simple);
        RationalInterval region(outer_simple, carl::BoundType::STRICT, inner_simple, carl::BoundType::STRICT);
        return carl::sample_stern_brocot(region, false);
    }

};


struct sample_stern_brocot {
    static Rational between(const RAN& l, const RAN& u) {
        Rational l_simple, u_simple, mid;
    
        if (l.is_numeric()) l_simple = carl::ceil(l.value());
        else l_simple = carl::ceil(l.interval().upper());

        if (u.is_numeric()) u_simple = carl::ceil(u.value());
        else u_simple = carl::ceil(u.interval().upper());

        // make sure l_simple is below u and u_simple is the first integer > u
        while (l_simple >= u) {
            if (l_simple < u_simple) u_simple = l_simple;
            l_simple = l_simple - 1;
        }

        for (std::size_t i = 0; i < apx_settings().n_sb_iterations;) {
            mid = mediant(l_simple, u_simple);
            if (mid >= u) {
                u_simple = mid;
            } else { // mid < u
                l_simple = mid;
                if (l < mid) ++i;
            }
        }

        return mid;
    }

    static Rational below(const RAN& inner, const RAN& outer) { return between(inner, outer); }
    static Rational above(const RAN& inner, const RAN& outer) { return between(outer, inner); }
};



struct sample_fixed_ratio {
    static  Rational above(const RAN& inner, const RAN& outer) {
        Rational apx_outer = approximate_RAN_below(outer);
        Rational apx_inner = approximate_RAN_above(inner);
        Rational upper_bound = (apx_settings().root_ratio_upper * apx_outer)
                             + ((1 - apx_settings().root_ratio_upper) * apx_inner);
        Rational lower_bound = (apx_settings().root_ratio_lower * apx_outer)
                             + ((1 - apx_settings().root_ratio_lower) * apx_inner);
        RationalInterval region(lower_bound, carl::BoundType::STRICT, upper_bound, carl::BoundType::STRICT);
        return carl::sample_stern_brocot(region, false);
    }

    static Rational below(const RAN& inner, const RAN& outer) {
        Rational apx_outer = approximate_RAN_above(outer);
        Rational apx_inner = approximate_RAN_below(inner);
        Rational lower_bound = (apx_settings().root_ratio_upper * apx_outer)
                             + ((1 - apx_settings().root_ratio_upper) * apx_inner);
        Rational upper_bound = (apx_settings().root_ratio_lower * apx_outer)
                             + ((1 - apx_settings().root_ratio_lower) * apx_inner);
        RationalInterval region(lower_bound, carl::BoundType::STRICT, upper_bound, carl::BoundType::STRICT);
        return carl::sample_stern_brocot(region, false);
    }
};

template<typename Root>
inline Rational approximate_root(const RAN& inner, const RAN& outer, bool below) {
    return below ? Root::below(inner, outer) : Root::below(inner, outer);
}

}