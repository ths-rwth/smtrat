#pragma once

#include <smtrat-modules/CoveringNGModule/CoveringNGModule.h>
#include <smtrat-modules/CoveringNGModule/CoveringNGModule.tpp>
#include <smtrat-modules/FPPModule/FPPModule.h>
#include <smtrat-modules/STropModule/STropModule.h>
#include <smtrat-solver/Manager.h>

namespace smtrat {

namespace internal {

struct CoveringNGSettings : CoveringNGSettingsDefault  {
    static constexpr cadcells::representation::CoveringHeuristic covering_heuristic = cadcells::representation::BIGGEST_CELL_COVERING_MIN_TDEG;
    static constexpr cadcells::operators::op op = cadcells::operators::op::mccallum_complete;
    struct formula_evaluation {
        using Type = covering_ng::formula::GraphEvaluation;
        static auto create(cadcells::datastructures::Projections& proj) {
            return Type(std::bind_front(covering_ng::formula::complexity::sotd, proj), 1, covering_ng::formula::complexity::min_tdeg, false, true, false, false);
        }
    };
};

}

/**
 * The most efficient CoveringNG strategy with preprocessing and subtropical. Is slightly slower than PPDefault.
 * 
 */
class CoveringNG_PPSTropDefault: public Manager {
public:
	CoveringNG_PPSTropDefault() : Manager() {
		setStrategy(
			addBackend<FPPModule<FPPSettings1>>({
                addBackend<STropModule<STropSettings3>>({
                    addBackend<CoveringNGModule<internal::CoveringNGSettings>>()
                })
            })
        );
	}
};
} // namespace smtrat
