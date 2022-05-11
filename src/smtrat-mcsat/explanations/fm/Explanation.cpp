#include "Explanation.h"
#include "ConflictGenerator.h"

namespace smtrat {
namespace mcsat {
namespace fm {

template<class Settings>
std::optional<mcsat::Explanation> Explanation<Settings>::operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, bool force_use_core) const {
    #ifdef SMTRAT_DEVOPTION_Statistics
    mStatistics.explanationCalled();
    #endif

    carl::Variables allowedVars(data.assignedVariables().begin(), data.assignedVariables().end());
    allowedVars.insert(var);

    std::vector<ConstraintT> bounds;

    if (!Settings::use_all_constraints || force_use_core) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explain conflict " <<  reason);
    
        for (const auto& b : reason) {
            if (b.type() != carl::FormulaType::CONSTRAINT) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-constraint bound " << b);
                continue;
            }
            // Note that FM can only eliminate one variable. Thus, only syntactically univariate bounds can be handled!
            if (!isSubset(b.variables(), allowedVars)) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-univariate bound " << b);
                continue;
            }
            assert(b.type() == carl::FormulaType::CONSTRAINT);
            bounds.emplace_back(b.constraint());
        }
    } else {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Explain conflict " <<  data.constraints());

        for (const auto& b : data.constraints()) {
            if (!isSubset(b.variables(), allowedVars)) {
                SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Discarding non-univariate bound " << b);
                continue;
            }
            assert(b.type() == carl::FormulaType::CONSTRAINT);
            bounds.emplace_back(b.constraint());
        }
    }

    std::optional<FormulasT> res = std::nullopt;
    // TODO add choice of Comparator to settings ...
    ConflictGenerator<DefaultComparator>(bounds, data.model(), var).generateExplanation([&](FormulasT expl) -> bool {
        res = expl;
        return true; // stop searching for conflicts after first conflict has been found
    });

    if (res) {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Found conflict " << *res);
        #ifdef SMTRAT_DEVOPTION_Statistics
        mStatistics.explanationSuccess();
        #endif
        return mcsat::Explanation(FormulaT(carl::FormulaType::OR, std::move(*res)));
    }
    else {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.fm", "Did not find a conflict");
        return std::nullopt;
    }
}

// Instantiations
template struct Explanation<DefaultSettings>;
template struct Explanation<IgnoreCoreSettings>;

}
}
}
