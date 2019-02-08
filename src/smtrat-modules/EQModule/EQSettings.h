/**
 * @file EQSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-10-19
 * Created on 2014-10-19.
 */


#pragma once
#include <unordered_map>
#include <map>
#include <ratio>
#include <cstdint>
#include "PairHash.h"

namespace smtrat
{
	struct EQSettings1
	{
		static constexpr auto moduleName = "EQModule<EQSettings1>";
		/*
		 * If we are collecting statistics, whether we collect hashing statistics (like the number of collisions, bucket insertions, hashtable size, ...).
		 */
		static constexpr bool collectHashStatistics = false;

		/**
		 * Whether to use class/rank compression into a single std::size_t or not.
		 * On 32-bit systems, this is automatically disabled (determined by sizeof(std::size_t)).
		 */
		static constexpr bool uf_use_compression = false;

		/**
		 * How long the maximum path may be (64 is safe, and this should not really affect speed).
		 */
		static constexpr std::size_t uf_max_traceback_length = 64;

		/*
		 * The capacity of our BFS ring-buffer queues. This size should mean that they never need to be reallocated.
		 * Note that the code correctly handles this case should it occur unexpectedly.
		 */
		static constexpr std::size_t initial_bfsqueue_capacity = 4096;

		/* the initial capacity of the hash bucket sets is 1 << hash_bucket_set_initial_capacity_shift */
		static constexpr std::size_t hash_bucket_set_initial_capacity_shift = 12;

		/* ideally, make the denominator a power of two for faster division */
		struct hash_bucket_set_load_factor {
			static constexpr std::size_t num = 1;
			static constexpr std::size_t den = 16;
		};
		
		/* add deductions for implicit edges that occur often enough */
		static constexpr bool addImplicitEdgeDeductions = false;

		/* add a deduction for an implicit edge after it occurred at least implicitEdgeDeductionRate times */
		static constexpr std::size_t implicitEdgeDeductionRate = 128;

		/* we add deductions for equalities of the formula that are not asserted currently */
		static constexpr bool deduceUnassignedLiterals = true;
		
		/* we check for deductions every testRateForDeductions call to isConsistent */
		static constexpr std::size_t testRateForDeductions = 4;
		
		/* the maximal number of infeasible subsets constructed in isConsistent */
		static constexpr std::size_t useMaxInfeasibleSubsets = 8;

		/* Flag for visualizing the graph */
		static constexpr bool visualiseGraphs = false;
		
		/* Flag for restricting visualization output only if the formula is inconsistent*/
		static constexpr bool visualiseOnlyWhenInconsistent = true;

		/* print all infeasible subsets as .smt2 formulas */
		static constexpr bool printInfeasibleSubsetFormulas = false;

		/* print information on bucket sets after assert/remove */
		static constexpr bool printBucketSets = false;

		/* print formulas in assert/remove to std::cout */
		static constexpr bool printFormulas = false;
	};

	struct EQSettingsForPreprocessing : public EQSettings1 {
		static constexpr auto moduleName = "EQModule<EQSettingsForPreprocessing>";
		static constexpr bool addImplicitEdgeDeductions = false;
		static constexpr bool deduceUnassignedLiterals = false;
		static constexpr std::size_t useMaxInfeasibleSubsets = 1;
		static constexpr bool printFormulas = false;
		static constexpr bool visualiseGraphs = false;
		static constexpr bool printBucketSets = false;
		static constexpr bool printInfeasibleSubsetFormulas = false;
		static constexpr bool collectHashStatistics = false;
	};
}
