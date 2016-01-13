#pragma once

#include "../../cli/ExitCodes.h"

#include <carl/util/platform.h>
#include <carl/util/Singleton.h>

#include <csignal>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/resource.h>

namespace smtrat {
namespace resource {

#ifdef __LINUX
inline void setCPULimit(std::size_t seconds) {
	rlimit rl;
    getrlimit(RLIMIT_CPU, &rl);
	rl.rlim_cur = seconds;
	setrlimit(RLIMIT_CPU, &rl);
}
inline std::size_t usedCPU() {
	return std::size_t(clock()) / CLOCKS_PER_SEC;
}
inline void resetCPULimit() {
	setCPULimit(RLIM_INFINITY);
}
inline void setMemoryLimit(std::size_t megabytes) {
	rlimit rl;
	getrlimit(RLIMIT_AS, &rl);
	rl.rlim_cur = megabytes * 1024 * 1024;
	setrlimit(RLIMIT_AS, &rl);
}
inline void resetMemoryLimit() {
	setMemoryLimit(RLIM_INFINITY);
}
inline void signalHandler(int signal) {
	if (signal == SIGXCPU) {
		std::cerr << "CPU resource out" << std::endl;
		std::exit(SMTRAT_EXIT_TIMEOUT);
	} else if (signal == ENOMEM) {
		std::cerr << "Mem resource out" << std::endl;
		std::exit(SMTRAT_EXIT_MEMOUT);
	} else {
		std::cerr << "Unknown abort in resource limitation module" << std::endl;
		std::exit(SMTRAT_EXIT_GENERALERROR);
	}
}
inline void installSignalHandler() {
	std::signal(SIGXCPU, signalHandler);
	std::signal(ENOMEM, signalHandler);
}
#else
inline void setCPULimit(std::size_t) {}
inline std::size_t usedCPU() {}
inline void resetCPULimit() {}
inline void setMemoryLimit(std::size_t) {}
inline void resetMemoryLimit() {}
#endif

class Limiter: public carl::Singleton<Limiter> {
private:
	std::size_t mTimeout;
public:
	void initialize() const {
		installSignalHandler();
	}
	void reset() {
		mTimeout = 0;
		resetTimeout();
		resetMemoryLimit();
	}
	void setMemout(std::size_t megabytes) const {
		setMemoryLimit(megabytes);
	}
	void resetMemout() const {
		resetMemoryLimit();
	}
	void setTimeout(std::size_t seconds) {
		mTimeout = seconds;
		resetTimeout();
	}
	void resetTimeout() const {
		if (mTimeout == 0) resetCPULimit();
		else setCPULimit(usedCPU() + mTimeout);
	}
};

}
}
