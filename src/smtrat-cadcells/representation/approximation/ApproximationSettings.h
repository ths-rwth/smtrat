namespace smtrat::cadcells::representation::approximation::settings {

enum ApxPoly {SIMPLE, LINEAR_GRADIENT, LINEAR_GRADIENT_MULTI, UNIVARIATE_TAYLOR, MULTIVARIATE_TAYLOR, HYPERPLANE};

enum ApxRoot {SAMPLE_MID, SIMPLE_REPRESENTATION, STERN_BROCOT, FIXED_RATIO, MAXIMIZE};

constexpr ApxPoly bound = ApxPoly::SIMPLE;
constexpr ApxPoly between = ApxPoly::SIMPLE;
constexpr ApxRoot root = ApxRoot::FIXED_RATIO;

const std::size_t taylor_deg = settings_module().get("apx_taylor_deg", 2);
// constexpr std::size_t hyperplane_dim = 0;

const std::size_t n_sb_iterations = settings_module().get("apx_taylor_deg", 2);
const double root_ratio_lower = settings_module().get("apx_root_ratio_l", 0.5);
const double root_ratio_upper = settings_module().get("apx_root_ratio_u", 0.9);

const std::size_t crit_max_considered = settings_module().get("apx_max_considered", 50);
const std::size_t crit_max_apx = settings_module().get("apx_max_apx", 50);
const std::size_t crit_max_constraint_involved = settings_module().get("apx_max_involved", 5);
const std::size_t crit_max_apx_per_poly = settings_module().get("apx_max_app", 5);
const std::size_t crit_degree_threshold = settings_module().get("apx_deg_threshold", 3);

const bool crit_level_enabled = settings_module().get("apx_level_enabled", false);
const bool crit_considered_count_enabled = settings_module().get("apx_considered_enabled", false);
const bool crit_apx_count_enabled = settings_module().get("apx_count_enabled", false);
const bool crit_single_degree_enabled = settings_module().get("apx_single_degree_enabled", false);
const bool crit_pair_degree_enabled = settings_module().get("apx_pair_degree_enabled", false);;
const bool crit_poly_apx_count_enabled = settings_module().get("apx_poly_count_enabled", false);
const bool crit_involved_count_enabled = settings_module().get("apx_involved_count_enabled", false);
const bool crit_side_degree_enabled = settings_module().get("apx_side_degree_enabled", false);

}