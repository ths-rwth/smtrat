namespace smtrat::cadcells::representation::approximation {

enum ApxPoly {SIMPLE, LINEAR_GRADIENT, TAYLOR, TAYLOR_LIN, MAXIMIZE};

enum ApxRoot {SAMPLE_MID, SIMPLE_REPRESENTATION, STERN_BROCOT, FIXED_RATIO};

struct ApxSettings {
    static constexpr ApxPoly bound = ApxPoly::SIMPLE;
    static constexpr ApxPoly between = ApxPoly::SIMPLE;
    static constexpr ApxRoot root = ApxRoot::SIMPLE_REPRESENTATION;

    const std::size_t taylor_deg = settings_module().get("apx_taylor_deg", (std::size_t)1);
    // constexpr std::size_t hyperplane_dim = 0;
    const std::size_t maximize_n_iter = settings_module().get("apx_maximize_iter", (std::size_t)5);

    const std::size_t n_sb_iterations   = settings_module().get("apx_sb_iter", (std::size_t)2);
    const double root_ratio_lower       = settings_module().get("apx_root_ratio_l", (double)0.75);
    const double root_ratio_upper       = settings_module().get("apx_root_ratio_u", (double)0.875);

    const std::size_t crit_max_considered           = settings_module().get("apx_max_considered", (std::size_t)20);
    const std::size_t crit_max_apx                  = settings_module().get("apx_max_apx", (std::size_t)50);
    const std::size_t crit_max_constraint_involved  = settings_module().get("apx_max_involved", (std::size_t)5);
    const std::size_t crit_max_apx_per_poly         = settings_module().get("apx_max_app", (std::size_t)5);
    const std::size_t crit_degree_threshold         = settings_module().get("apx_deg_threshold", (std::size_t)5);

    const bool crit_level_enabled               = settings_module().get("apx_level_enabled", false);
    const bool crit_considered_count_enabled    = settings_module().get("apx_considered_enabled", false);
    const bool crit_apx_count_enabled           = settings_module().get("apx_count_enabled", true);
    const bool crit_single_degree_enabled       = settings_module().get("apx_single_degree_enabled", true);
    const bool crit_pair_degree_enabled         = settings_module().get("apx_pair_degree_enabled", false);
    const bool crit_poly_apx_count_enabled      = settings_module().get("apx_poly_count_enabled", false);
    const bool crit_involved_count_enabled      = settings_module().get("apx_involved_count_enabled", false);
    const bool crit_side_degree_enabled         = settings_module().get("apx_side_degree_enabled", false);
};

inline const ApxSettings& apx_settings() {
    static ApxSettings s;
    return s;
}

}