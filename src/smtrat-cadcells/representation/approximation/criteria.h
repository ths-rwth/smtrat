namespace smtrat::cadcells::representation::approximation::criteria {

using IR = datastructures::IndexedRoot;

static constexpr std::size_t max_count = 100;
static constexpr std::size_t max_involved = 15;
static constexpr std::size_t critical_degree = 5;

class ApxCriteria_Detail {
    private:
        std::size_t m_count = 0;
        bool m_cell_apx = false;
        std::unordered_map<FormulaT, std::size_t> m_involved;
    public:
        ApxCriteria_Detail () {}

        static ApxCriteria_Detail& get_instance() {
            static ApxCriteria_Detail instance = ApxCriteria_Detail();
            return instance;
        }

        void inform_apx() {
            m_cell_apx = true;
        }

        void new_cell() {
            m_cell_apx = false;
        }

        bool count_ok() {
            if (m_count < max_count) {
                if (m_cell_apx) ++m_count;
                return true;
            } else {
                #ifdef SMTRAT_DEVOPTION_Statistics
                    OCApproximationStatistics::get_instance().maxIterationsReached();
                #endif
                return false;
            }
        }

        bool involved_ok(const FormulasT& constraints) {
            return true;
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
};

bool cell(const FormulasT& constraints) {
    ApxCriteria_Detail& ad = ApxCriteria_Detail::get_instance();
    ad.new_cell();
    return ad.count_ok() && ad.involved_ok(constraints);
}

bool level() {
    return true;
}

bool single(datastructures::Projections& proj, const IR& ir) {
    return proj.degree(ir.poly) > critical_degree;
}

bool pair(datastructures::Projections& proj, const IR& ir_l, const IR& ir_u) {
    return proj.degree(ir_l.poly) + proj.degree(ir_u.poly) > critical_degree;
}

template <typename T>
bool all(datastructures::SampledDerivationRef<T>& der) {
    assert(false); // TODO
    return false;
}

}