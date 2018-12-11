/**
 * @file NewCADSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#pragma once

#include <lib/datastructures/cad/Settings.h>

namespace smtrat {
namespace cad {
	/// Mixin that provides settings for incrementality and backtracking.
	template<Incrementality I, Backtracking B>
	struct IncrementalityMixin {
		static constexpr Incrementality incrementality = I;
		static constexpr Backtracking backtracking = B;
	};
	using IncrementalityNO = IncrementalityMixin<Incrementality::NONE,Backtracking::ORDERED>;
	using IncrementalityNU = IncrementalityMixin<Incrementality::NONE,Backtracking::UNORDERED>;
	using IncrementalitySO = IncrementalityMixin<Incrementality::SIMPLE,Backtracking::ORDERED>;
	using IncrementalitySU = IncrementalityMixin<Incrementality::SIMPLE,Backtracking::UNORDERED>;
	using IncrementalityF = IncrementalityMixin<Incrementality::FULL,Backtracking::UNORDERED>;
	using IncrementalityFO = IncrementalityMixin<Incrementality::FULL,Backtracking::UNORDERED>;
	using IncrementalityEQ = IncrementalityMixin<Incrementality::FULL,Backtracking::HIDE>;
	using IncrementalityFU = IncrementalityMixin<Incrementality::FULL,Backtracking::UNORDERED>;
	
	/// Mixin that provides settings for the projection operator.
	template<ProjectionType P>
	struct ProjectionMixin {
		static constexpr ProjectionType projectionOperator = P;
	};
	using ProjectionBrown = ProjectionMixin<ProjectionType::Brown>;
	using ProjectionMcCallum = ProjectionMixin<ProjectionType::McCallum>;
	
	/// Mixin that provides settings for the sample comparison.
	template<SampleCompareStrategy SCS, FullSampleCompareStrategy FSCS>
	struct SampleCompareMixin {
		static constexpr cad::SampleCompareStrategy sampleComparator = SCS;
		static constexpr cad::FullSampleCompareStrategy fullSampleComparator = FSCS;
	};
	using SampleCompareValue = SampleCompareMixin<SampleCompareStrategy::Value, FullSampleCompareStrategy::Value>;
	using SampleCompareType = SampleCompareMixin<SampleCompareStrategy::Type, FullSampleCompareStrategy::Type>;
	
	using SampleCompareT = SampleCompareMixin<SampleCompareStrategy::T, FullSampleCompareStrategy::T>;
	using SampleCompareTLSA = SampleCompareMixin<SampleCompareStrategy::TLSA, FullSampleCompareStrategy::T>;
	using SampleCompareTSA = SampleCompareMixin<SampleCompareStrategy::TSA, FullSampleCompareStrategy::T>;
	using SampleCompareTS = SampleCompareMixin<SampleCompareStrategy::TS, FullSampleCompareStrategy::T>;
	using SampleCompareLT = SampleCompareMixin<SampleCompareStrategy::LT, FullSampleCompareStrategy::T>;
	using SampleCompareLTA = SampleCompareMixin<SampleCompareStrategy::LTA, FullSampleCompareStrategy::T>;
	using SampleCompareLTS = SampleCompareMixin<SampleCompareStrategy::LTS, FullSampleCompareStrategy::T>;
	using SampleCompareLTSA = SampleCompareMixin<SampleCompareStrategy::LTSA, FullSampleCompareStrategy::T>;
	using SampleCompareLS = SampleCompareMixin<SampleCompareStrategy::LS, FullSampleCompareStrategy::T>;
	using SampleCompareS = SampleCompareMixin<SampleCompareStrategy::S, FullSampleCompareStrategy::T>;
	
	/// Mixin that provides settings for the projection order.
	template<ProjectionCompareStrategy PCS>
	struct ProjectionOrderMixin {
		static constexpr cad::ProjectionCompareStrategy projectionComparator = PCS;
	};

	using ProjectionOrderDefault = ProjectionOrderMixin<ProjectionCompareStrategy::Default>;
	using ProjectionOrderD = ProjectionOrderMixin<ProjectionCompareStrategy::D>;
	using ProjectionOrderPD = ProjectionOrderMixin<ProjectionCompareStrategy::PD>;
	using ProjectionOrderSD = ProjectionOrderMixin<ProjectionCompareStrategy::SD>;
	using ProjectionOrderlD = ProjectionOrderMixin<ProjectionCompareStrategy::lD>;
	using ProjectionOrderLD = ProjectionOrderMixin<ProjectionCompareStrategy::LD>;
	
	/// Mixin that provides settings for MIS generation
	template<MISHeuristic MIS>
	struct MISHeuristicMixin {
		static constexpr cad::MISHeuristic misHeuristic = MIS;
	};
	using MISHeuristicTrivial = MISHeuristicMixin<MISHeuristic::TRIVIAL>;
	using MISHeuristicGreedy = MISHeuristicMixin<MISHeuristic::GREEDY>;
}

	struct NewCADBaseSettings: cad::MISHeuristicGreedy {
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::Default;
		static constexpr cad::RootSplittingStrategy rootSplittingStrategy = cad::RootSplittingStrategy::DEFAULT;
		static constexpr cad::CoreHeuristic coreHeuristic = cad::CoreHeuristic::PreferSampling;
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = false;
		static constexpr bool debugProjection = false;
		static constexpr bool debugStepsToTikz = false;
		static constexpr bool force_nonincremental = false;

		static constexpr bool semiRestrictedProjection = false;
		static constexpr bool restrictedIfPossible = true;
	};
	
	struct NewCADSettingsNaive: NewCADBaseSettings, cad::IncrementalityNO, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<Naive>";
		static constexpr bool force_nonincremental = true;
	};
	
	struct NewCADSettingsNO: NewCADBaseSettings, cad::IncrementalityNO, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADNO>";
	};
	
	struct NewCADSettingsNU: NewCADBaseSettings, cad::IncrementalityNU, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADNU>";
	};
	
	struct NewCADSettingsSO: NewCADBaseSettings, cad::IncrementalitySO, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADSO>";
	};
	struct NewCADSettingsSU: NewCADBaseSettings, cad::IncrementalitySU, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADSU>";
	};
	
	struct NewCADSettingsFU: NewCADBaseSettings, cad::IncrementalityFU, cad::ProjectionBrown, cad::SampleCompareLT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADFU>";
	};
	
	//
	// Settings to test different sampling heuristics
	//
	struct NewCADSettingsFU_SC: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SC>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::Center;
	};
	struct NewCADSettingsFU_SI: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SI>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::CenterInt;
	};
	struct NewCADSettingsFU_SL: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SL>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::LeftInt;
	};
	struct NewCADSettingsFU_SR: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SR>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::RightInt;
	};
	struct NewCADSettingsFU_SZ: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SZ>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::ZeroInt;
	};
	struct NewCADSettingsFU_SInf: NewCADSettingsFU {
		static constexpr auto moduleName = "NewCADModule<NewCADFU_SInf>";
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::InftyInt;
	};
	// end of sampling heuristics
	
	//
	// Settings to test different lifting order heuristics
	//
	struct NewCADBaseSettingsLO: NewCADBaseSettings, cad::IncrementalityFU, cad::ProjectionBrown, cad::ProjectionOrderDefault {};
	
	struct NewCADSettings_LOType: NewCADBaseSettingsLO, cad::SampleCompareType {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOType>";
	};
	struct NewCADSettings_LOT: NewCADBaseSettingsLO, cad::SampleCompareT {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOT>";
	};
	struct NewCADSettings_LOTLSA: NewCADBaseSettingsLO, cad::SampleCompareTLSA {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOTLSA>";
	};
	struct NewCADSettings_LOTSA: NewCADBaseSettingsLO, cad::SampleCompareTSA {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOTSA>";
	};
	struct NewCADSettings_LOTS: NewCADBaseSettingsLO, cad::SampleCompareTS {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOTS>";
	};
	struct NewCADSettings_LOLT: NewCADBaseSettingsLO, cad::SampleCompareLT {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOLT>";
	};
	struct NewCADSettings_LOLTA: NewCADBaseSettingsLO, cad::SampleCompareLTA {
		static constexpr auto moduleName = "NewCADModule<NewCADLOLTA>";
	};
	struct NewCADSettings_LOLTS: NewCADBaseSettingsLO, cad::SampleCompareLTS {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOLTS>";
	};
	struct NewCADSettings_LOLTSA: NewCADBaseSettingsLO, cad::SampleCompareLTSA {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOLTSA>";
	};
	struct NewCADSettings_LOLS: NewCADBaseSettingsLO, cad::SampleCompareLS {
		static constexpr auto moduleName = "NewCADModule<NewCADLOLS>";
	};
	struct NewCADSettings_LOS: NewCADBaseSettingsLO, cad::SampleCompareS {
		static constexpr auto moduleName = "NewCADModule<NewCAD_LOS>";
	};
	// end of lifting order heuristics
	
	//
	// Settings to test different projection order heuristics
	//
	struct NewCADBaseSettingsPO: NewCADBaseSettings, cad::IncrementalityFU, cad::ProjectionBrown, cad::SampleCompareT {};
	
	struct NewCADSettings_POD: NewCADBaseSettingsPO, cad::ProjectionOrderD {
		static constexpr auto moduleName = "NewCADModule<NewCAD_POD>";
	};
	struct NewCADSettings_POPD: NewCADBaseSettingsPO, cad::ProjectionOrderPD {
		static constexpr auto moduleName = "NewCADModule<NewCAD_POPD>";
	};
	struct NewCADSettings_POSD: NewCADBaseSettingsPO, cad::ProjectionOrderSD {
		static constexpr auto moduleName = "NewCADModule<NewCAD_POSD>";
	};
	struct NewCADSettings_POlD: NewCADBaseSettingsPO, cad::ProjectionOrderlD {
		static constexpr auto moduleName = "NewCADModule<NewCAD_POlD>";
	};
	struct NewCADSettings_POLD: NewCADBaseSettingsPO, cad::ProjectionOrderLD {
		static constexpr auto moduleName = "NewCADModule<NewCAD_POLD>";
	};
	// end of projection order heuristics
	
	struct NewCADSettingsF1: NewCADBaseSettings, cad::IncrementalityF, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADF>";
		static constexpr std::size_t trivialSampleRadius = 1;
	};
	struct NewCADSettingsFO1: NewCADBaseSettings, cad::IncrementalityFO, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADFO>";
		static constexpr std::size_t trivialSampleRadius = 1;
	};
	struct NewCADSettingsFOS: NewCADBaseSettings, cad::IncrementalityFO, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADFO>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
	};


	struct NewCADSettingsInterleave: NewCADSettingsFOS {
		static constexpr auto moduleName = "NewCADModule<NewCADInterleave>";
		static constexpr cad::CoreHeuristic coreHeuristic = cad::CoreHeuristic::Interleave;
	};

	struct NewCADSettingsEQ_B: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_B>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = false;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_BD: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BD>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = false;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_R: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_R>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_RD: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_RD>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_RI: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_RI>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_RID: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_RID>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_S: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_S>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_SD: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_SD>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_BR: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BR>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_BRD: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BRD>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_BRI: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionMcCallum, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BRI>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_BRID: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionMcCallum, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BRID>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = false;
	};
	struct NewCADSettingsEQ_BS: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BS>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_BSD: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BSD>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = false;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_SI: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_SI>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_SID: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_SID>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_BSI: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionMcCallum, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BSI>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = false;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = true;
	};
	struct NewCADSettingsEQ_BSID: NewCADBaseSettings, cad::IncrementalityEQ, cad::ProjectionMcCallum, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEQ_BSID>";
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = true;
		static constexpr bool restrictProjectionByEC = true;
		static constexpr bool deletePolynomials = true;
		static constexpr bool interruptions = true;
		static constexpr bool semiRestrictedProjection = true;
	};
	
	struct NewCADSettingsFV: NewCADBaseSettings, cad::IncrementalityF, cad::ProjectionBrown, cad::SampleCompareValue, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADFV>";
	};
	struct NewCADSettingsFOV: NewCADBaseSettings, cad::IncrementalityFO, cad::ProjectionBrown, cad::SampleCompareValue, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADFOV>";
	};
	
	struct NewCADSettingsEnumerateAll: NewCADBaseSettings, cad::IncrementalityNO, cad::ProjectionBrown, cad::SampleCompareT, cad::ProjectionOrderDefault {
		static constexpr auto moduleName = "NewCADModule<NewCADEnumAll>";
		static constexpr cad::CoreHeuristic coreHeuristic = cad::CoreHeuristic::EnumerateAll;
	};
	
	struct NewCADSettingsConfigured {
		static constexpr auto moduleName = "NewCADModule<NewCADConfigured>";
		static constexpr cad::Incrementality incrementality = cad::Incrementality::FULL;
		static constexpr cad::Backtracking backtracking = cad::Backtracking::UNORDERED;
		
		static constexpr cad::ProjectionType projectionOperator = cad::ProjectionType::Brown;
		static constexpr cad::CoreHeuristic coreHeuristic = cad::CoreHeuristic::PreferProjection;
		
		static constexpr cad::MISHeuristic misHeuristic = cad::MISHeuristic::GREEDY;
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = false;
		static constexpr bool debugProjection = false;
		static constexpr bool debugStepsToTikz = false;
		static constexpr bool force_nonincremental = false;
		
		static constexpr cad::ProjectionCompareStrategy projectionComparator = cad::ProjectionCompareStrategy::Default;
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::Default;
		static constexpr cad::SampleCompareStrategy sampleComparator = cad::SampleCompareStrategy::Default;
		static constexpr cad::FullSampleCompareStrategy fullSampleComparator = cad::FullSampleCompareStrategy::Default;
		static constexpr cad::RootSplittingStrategy rootSplittingStrategy = cad::RootSplittingStrategy::DEFAULT;
	};
}
