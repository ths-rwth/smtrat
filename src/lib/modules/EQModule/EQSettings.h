/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
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
	struct HashFunctions {
		template<std::size_t> struct LARGE_CONSTANTS_;

		typedef LARGE_CONSTANTS_<sizeof(std::size_t)> LARGE_CONSTANTS;

		struct SIMPLE_ADD_MULT_HASHER {};

		struct SIMPLE_PAIR_COMBINE_HASHER {};
	};

	template<> struct HashFunctions::LARGE_CONSTANTS_<4> {
		static constexpr std::size_t factors[8] = {
			UINT32_C(3288800093),
			UINT32_C(267968795),
			UINT32_C(1768103087),
			UINT32_C(2643043759),
			UINT32_C(3051305475),
			UINT32_C(2022871811),
			UINT32_C(1457296549),
			UINT32_C(2117878904)
		};

		static constexpr std::size_t additive[8] = {
			UINT32_C(1641871010),
			UINT32_C(950975399),
			UINT32_C(1915621737),
			UINT32_C(3383503198),
			UINT32_C(1799877594),
			UINT32_C(103577608),
			UINT32_C(2772910263),
			UINT32_C(4033601987)
		};
	};

	template<> struct HashFunctions::LARGE_CONSTANTS_<8> {
		static constexpr std::size_t factors[8] = {
			UINT64_C(17505341168218075185),
			UINT64_C(11766632334972576027),
			UINT64_C(20321231558827191),
			UINT64_C(6669636300788637967),
			UINT64_C(1274660710519722977),
			UINT64_C(3049996924038469891),
			UINT64_C(13132168464761848415),
			UINT64_C(6458782492647728569)
		};

		static constexpr std::size_t additive[8] = {
			UINT64_C(745557436620299238),
			UINT64_C(1383624249020429893),
			UINT64_C(18142254430362950227),
			UINT64_C(17215480335179720365),
			UINT64_C(1963882785427909144),
			UINT64_C(16444188889433461361),
			UINT64_C(1183983407368020021),
			UINT64_C(13270416360825815309)
		};
	};

	struct EQSettings1
	{
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
		
		/* determines the hash function used in the hash_bucket_sets */
		typedef HashFunctions::SIMPLE_ADD_MULT_HASHER FunctionInstanceHash;
		
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
