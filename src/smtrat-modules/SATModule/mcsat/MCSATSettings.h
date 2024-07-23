#pragma once

#include <smtrat-mcsat/assignments/arithmetic/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/smtaf/AssignmentFinder.h>
#include <smtrat-mcsat/assignments/SequentialAssignment.h>
#include <smtrat-mcsat/explanations/ParallelExplanation.h>
#include <smtrat-mcsat/explanations/SequentialExplanation.h>
#include <smtrat-mcsat/explanations/icp/Explanation.h>
#include <smtrat-mcsat/explanations/nlsat/Explanation.h>
#include <smtrat-mcsat/explanations/onecellcad/recursive/Explanation.h>
#include <smtrat-mcsat/explanations/onecellcad/levelwise/Explanation.h>
#include <smtrat-mcsat/explanations/vs/Explanation.h>
#include <smtrat-mcsat/explanations/fm/Explanation.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>
#include <smtrat-mcsat/explanations/onecell/Explanation.h>

namespace smtrat {
namespace mcsat {

struct Base {
	static constexpr bool early_evaluation = false;
};

struct MCSATSettingsDefault : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecell::Explanation<onecell::DefaultSettings>>;
};

struct MCSATSettingsAPX : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,
													 icp::Explanation,
													 vs::Explanation,
													 onecell::Explanation<onecell::ApproximationSettings>,
													 onecell::Explanation<onecell::DefaultSettings>>;
};

struct MCSATSettingsBCCov : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,
													 icp::Explanation,
													 vs::Explanation,
													 onecell::Explanation<onecell::BCCoveringSettings>,
													 onecell::Explanation<onecell::DefaultSettings>>;
};

struct MCSATSettingsNL : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation, nlsat::Explanation>;
};

//OneCell only
struct MCSATSettingsOC : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCNN : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<
	        onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::NoHeuristic>,
	        nlsat::Explanation>;
};
struct MCSATSettingsOCNNASC : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCNNDSC : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCLWH11 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH12  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH13 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH21 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH22 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH23 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH31 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH32 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH33 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH11 : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH12 : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH13 : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
	        onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCNNASC : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCNNDSC : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeDescending>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCPARALLEL : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    //TODO add parallel explanation functionality
    /*
    using ExplanationBackend = SequentialExplanation<
                                    FastParallelExplanation<
                                        fm::Explanation<fm::DefaultSettings>,
                                        icp::Explanation,
                                        vs::Explanation>,
                                    FastParallelExplanation<
                                        onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification>,
                                        onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>,
                                        onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>,
                                        onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>,
                                        nlsat::Explanation >>;
    */
    using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSATSettingsOCPARALLEL : Base  {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    //TODO add parallel explanation functionality
    /*using ExplanationBackend = FastParallelExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification>,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>,
            nlsat::Explanation >;
    */
    using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSATSettingsOCNew : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecell::Explanation<onecell::DefaultSettings>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCNew : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecell::Explanation<onecell::DefaultSettings>,nlsat::Explanation>;
};

struct MCSATSettingsVSOCNew : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<vs::Explanation,onecell::Explanation<onecell::DefaultSettings>,nlsat::Explanation>;
};
struct MCSATSettingsFMOCNew : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,onecell::Explanation<onecell::DefaultSettings>,nlsat::Explanation>;
};

struct MCSATSettingsFMICPVSOCNewOC : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecell::Explanation<onecell::DefaultSettings>,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>,nlsat::Explanation>;
};
struct MCSATSettingsFMVSOC : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOC  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPOC : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSATSettingsFMNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	// using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,nlsat::Explanation>;
};

struct MCSATSettingsVSNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsFMVSNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsICPNL : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<icp::Explanation,nlsat::Explanation>;
};

struct MCSAT_AF_NL  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSAT_AF_OCNL  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMOCNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMICPOCNL  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMICPVSOCNL : Base  {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMVSOCNL  : Base {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};

struct MCSAT_SMT_FMOCNL : Base  {
	using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};

}
}
