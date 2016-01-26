/**
 * @file  BenchmarkStatus.h
 * @author Sebastian Junges
 *
 *
 */

#pragma once

#include <iostream>
#include <map>

#include "results/BenchmarkResult.h"

namespace benchmax {

enum BenchmarkStatus
{
	BS_SAT = 0, BS_UNSAT = 1, BS_UNKNOWN = 2, BS_INVALID = -1
};

BenchmarkStatus benchmarkStatusFromParser(int parserStatus);
std::string benchmarkStatusToString(BenchmarkStatus status);

enum BenchmarkResultCode
{
	BR_SAT = 0, BR_UNSAT = 1, BR_UNKNOWN = 2, BR_INVALID = -1, BR_TIMEOUT = 3, BR_MEMOUT = 4, BR_WRONG = 5, BR_ABORT = 6, BR_SEGFAULT = 7,
	BR_SOLVERERROR = 8, BR_UNEXPECTEDERROR = 9, BR_NORESULT = 100
};

std::string benchmarkResultToString(BenchmarkResultCode result);

enum ValidationResult { NOTVALIDATED = -1, FOUNDERROR = 1, OKAY = 0 };

}
