namespace smtrat::cadcells::representation::approximation::criteria {

using IR = datastructures::IndexedRoot;

static constexpr std::size_t max_count = 50;
static constexpr std::size_t max_involved = 15;
static constexpr std::size_t max_apx_per_poly = 15;
static constexpr std::size_t critical_degree = 4;
static constexpr bool skip_level_one = true;

class ApxCriteria_Detail {
    private:
        std::size_t m_count = 0;
        bool m_cell_apx = false;
        std::unordered_map<FormulaT, std::size_t> m_involved;
        std::map<datastructures::PolyRef, std::size_t> m_apx_polys;
    public:
        ApxCriteria_Detail () {}

        static ApxCriteria_Detail& get_instance() {
            static ApxCriteria_Detail instance = ApxCriteria_Detail();
            return instance;
        }

        void inform_apx(datastructures::PolyRef p) {
            ++m_apx_polys[p];
            if (!m_cell_apx) {
                ++m_count;
                m_cell_apx = true;
            }
        }

        void new_cell() {
            m_cell_apx = false;
        }

        bool count_ok() {
            if (m_count < max_count) {
                return true;
            } else {
                #ifdef SMTRAT_DEVOPTION_Statistics
                    OCApproximationStatistics::get_instance().maxIterationsReached();
                #endif
                return false;
            }
        }

        bool involved_ok(const FormulasT& constraints) {
            bool result = true;
            for (const FormulaT c : constraints) {
                ++m_involved[c];
                #ifdef SMTRAT_DEVOPTION_Statistics
                    if (m_involved[c] == max_involved)
                        OCApproximationStatistics::get_instance().involvedTooOften();
                #endif
                if (m_involved[c] >= max_involved) result = false;
            }
            return result;
        }

        bool poly_ok(const datastructures::PolyRef& p) {
            return m_apx_polys[p] > max_apx_per_poly;
        }
};

bool cell(const FormulasT& constraints) {
    ApxCriteria_Detail& ad = ApxCriteria_Detail::get_instance();
    ad.new_cell();
    return ad.count_ok() && ad.involved_ok(constraints);
}

bool level(std::size_t l) {
    if (skip_level_one) return l > 1;
    return true;
}

bool single(datastructures::Projections& proj, const IR& ir) {
    bool res = true;
    res &= (proj.degree(ir.poly) > critical_degree);
    res &= ApxCriteria_Detail::get_instance().poly_ok(ir.poly);
    return res;
}

bool pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
    if (proj.degree(ir_l.poly) < 2 || proj.degree(ir_u.poly) < 2) return false;
    return proj.degree(ir_l.poly) * proj.degree(ir_u.poly) > critical_degree;
}

bool side(datastructures::Projections& proj, const IR& ir, datastructures::RootMap::const_iterator start, datastructures::RootMap::const_iterator end) {
    for(auto it = start; it != end; it++) {
        for (const auto& ir_outer : it->second) {
            if (pair(proj, ir, ir_outer)) return true;
        }
    }
    return false;
}

}