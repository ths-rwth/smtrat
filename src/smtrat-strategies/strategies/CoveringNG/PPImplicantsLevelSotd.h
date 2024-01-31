#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {


namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            auto fe_implicant_ordering = covering_ng::formula::complexity::min_level_min_sotd;
            std::size_t fe_results = 1;
            auto fe_constraint_ordering = covering_ng::formula::complexity::min_tdeg;
            bool fe_stop_evaluation_on_conflict = false;
            bool fe_preprocess = true;
            bool fe_postprocess = false;
            auto fe_boolean_exploration = covering_ng::formula::GraphEvaluation::PROPAGATION;
            return Type(std::bind_front(fe_implicant_ordering, proj), fe_results, fe_constraint_ordering, fe_stop_evaluation_on_conflict, fe_preprocess, fe_postprocess, fe_boolean_exploration);
        }
    };
};

}

class CoveringNG_PPImplicantsLevelSotd: public Manager {
public:
	CoveringNG_PPImplicantsLevelSotd() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
