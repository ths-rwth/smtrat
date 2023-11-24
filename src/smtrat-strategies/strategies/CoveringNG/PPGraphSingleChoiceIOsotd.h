#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::sotd, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

}

class CoveringNG_PPGraphSingleChoiceIOsotd: public Manager {
public:
	CoveringNG_PPGraphSingleChoiceIOsotd() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
            })
        );
	}
};
} // namespace smtrat
