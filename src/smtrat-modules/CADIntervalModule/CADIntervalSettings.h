/**
 * @file CADIntervalSettings.h
 * @author Hanna Franzen <hanna.franzen@rwth-aachen.de>
 *
 * @version 2019-02-20
 * Created on 2019-02-20.
 */

#pragma once

namespace smtrat
{
	struct CADIntervalSettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "CADIntervalModule<CADIntervalSettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};

	/**@todo adopted from NewCADSettings, this should be ok. recheck */
	namespace cad {
		template<MISHeuristic MIS>
		struct MISHeuristicMixin {
			static constexpr cad::MISHeuristic misHeuristic = MIS;
		};
		using MISHeuristicGreedy = MISHeuristicMixin<MISHeuristic::GREEDY>;
	}

	/**@todo adopted from NewCADSettings, recheck whether to keep all of these */
	struct CADIntervalBaseSettings: cad::MISHeuristicGreedy {
		static constexpr cad::SampleHeuristic sampleHeuristic = cad::SampleHeuristic::Default;
		static constexpr cad::RootSplittingStrategy rootSplittingStrategy = cad::RootSplittingStrategy::DEFAULT;
		static constexpr cad::CoreIntervalBasedHeuristic coreHeuristic = cad::CoreIntervalBasedHeuristic::UnsatCover;
		static constexpr std::size_t trivialSampleRadius = 1;
		static constexpr bool simplifyProjectionByBounds = false;
		static constexpr bool restrictProjectionByEC = false;
		static constexpr bool debugProjection = false;
		static constexpr bool debugStepsToTikz = false;
		static constexpr bool force_nonincremental = false;
		static constexpr bool split_for_integers = true;

		static constexpr bool semiRestrictedProjection = false;
		static constexpr bool restrictedIfPossible = true;

		static constexpr bool pp_disable_variable_elimination = true;
		static constexpr bool pp_disable_resultants = true;
	};

	struct CADIntervalSettingsBase: CADIntervalBaseSettings {
		static constexpr auto moduleName = "CADIntervalModule<Base>";
	};

}
