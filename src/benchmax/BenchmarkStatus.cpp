
#include "BenchmarkStatus.h"

namespace benchmax {

BenchmarkStatus benchmarkStatusFromParser(int parserStatus)
{
	switch(parserStatus)
	{
		case 0:
			return BS_UNSAT;
		case 1:
			return BS_SAT;
		case -1:
			return BS_UNKNOWN;
		default:
			std::cerr << "Invalid parser status obtained\n";
			return BS_INVALID;
	}
}

std::string benchmarkStatusToString(BenchmarkStatus status)
{
	switch(status)
	{
		case BS_SAT:
			return "sat";
		case BS_UNSAT:
			return "unsat";
		case BS_UNKNOWN:
			return "unknown";
		case BS_INVALID:
			return "invalid";
		default:
			std::cerr << "Invalid result type" << std::endl;
			return "";
	}
}

std::string benchmarkResultToString(BenchmarkResultCode result)
{
	switch(result)
	{
		case BR_SAT:
			return "sat";
		case BR_UNSAT:
			return "unsat";
		case BR_UNKNOWN:
			return "unknown";
		case BR_INVALID:
			return "invalid";
		case BR_TIMEOUT:
			return "timeout";
		case BR_MEMOUT:
			return "memout";
		case BR_WRONG:
			return "wrong";
		case BR_ABORT:
			return "abort";
		case BR_SEGFAULT:
			return "segfault";
		case BR_SOLVERERROR:
			return "error";
		case BR_UNEXPECTEDERROR:
			return "unexpected error";
		case BR_NORESULT:
			return "none";
		default:
			std::cerr << "Invalid result type" << std::endl;
			return "";
	}
}
}
