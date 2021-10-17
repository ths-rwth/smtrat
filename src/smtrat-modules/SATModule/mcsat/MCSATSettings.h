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

struct MCSATSettingsNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation, nlsat::Explanation>;
};

//OneCell only
struct MCSATSettingsOC {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCNN {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<
	        onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::NoHeuristic>,
	        nlsat::Explanation>;
};
struct MCSATSettingsOCNNASC {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCNNDSC {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>,
            nlsat::Explanation>;
};
struct MCSATSettingsOCLWH11 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH12 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH13 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH21 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH22 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH23 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic2,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH31 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH32 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsOCLWH33 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic3,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH11 {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic1>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH12 {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic2>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCLWH13 {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
	        onecellcad::levelwise::Explanation<onecellcad::levelwise::SectionHeuristic1,onecellcad::levelwise::SectorHeuristic3>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCNNASC {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeAscending>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCNNDSC {
    using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    //using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
    using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,
            onecellcad::recursive::Explanation<onecellcad::recursive::DontCoverNullification, onecellcad::recursive::DegreeDescending>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOCPARALLEL {
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
struct MCSATSettingsOCPARALLEL {
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
struct MCSATSettingsOCNew {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
    using ExplanationBackend = SequentialExplanation<onecell::Explanation, nlsat::Explanation>;
};
struct MCSATSettingsFMVSOC {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSATSettingsFMICPVSOC {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	//using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSATSettingsFMNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	// using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,nlsat::Explanation>;
};

struct MCSATSettingsVSNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsFMVSNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,nlsat::Explanation>;
};

struct MCSATSettingsICPNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<icp::Explanation,nlsat::Explanation>;
};

struct MCSAT_AF_NL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<nlsat::Explanation>;
};
struct MCSAT_AF_OCNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMOCNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMICPOCNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMICPVSOCNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,icp::Explanation,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};
struct MCSAT_AF_FMVSOCNL {
	using AssignmentFinderBackend = arithmetic::AssignmentFinder;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,vs::Explanation,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};

struct MCSAT_SMT_FMOCNL {
	using AssignmentFinderBackend = SequentialAssignment<smtaf::AssignmentFinder<smtaf::DefaultSettings>,arithmetic::AssignmentFinder>;
	using ExplanationBackend = SequentialExplanation<fm::Explanation<fm::DefaultSettings>,onecellcad::recursive::Explanation<onecellcad::recursive::CoverNullification, onecellcad::recursive::NoHeuristic>, nlsat::Explanation>;
};

}
}
