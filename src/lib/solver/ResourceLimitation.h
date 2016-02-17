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
inline std::size_t getCPULimit() {
	rlimit rl;
    getrlimit(RLIMIT_CPU, &rl);
	return rl.rlim_cur;
}
inline std::size_t usedCPU() {
	return std::size_t(clock()) / CLOCKS_PER_SEC;
}
inline void setMemoryLimit(std::size_t megabytes) {
	rlimit rl;
	getrlimit(RLIMIT_AS, &rl);
	rl.rlim_cur = megabytes * 1024 * 1024;
	setrlimit(RLIMIT_AS, &rl);
}

inline std::size_t getMemoryLimit() {
	rlimit rl;
    getrlimit(RLIMIT_AS, &rl);
	return rl.rlim_cur;
}
inline void signalHandler(int signal) {
	if (signal == SIGXCPU) {
		std::cerr << "(error \"CPU resource out\")" << std::endl;
		std::quick_exit(SMTRAT_EXIT_TIMEOUT);
	} else if (signal == ENOMEM) {
		std::cerr << "(error \"Memory resource out\")" << std::endl;
		std::quick_exit(SMTRAT_EXIT_MEMOUT);
	} else {
		std::cerr << "(error \"Unknown abort in resource limitation module\")" << std::endl;
		std::quick_exit(SMTRAT_EXIT_GENERALERROR);
	}
}
inline void installSignalHandler() {
	std::signal(SIGXCPU, signalHandler);
	std::signal(ENOMEM, signalHandler);
}
#else
inline void setCPULimit(std::size_t) {}
inline std::size_t getCPULimit() { return 0; }
inline std::size_t usedCPU() { return 0; }
inline void setMemoryLimit(std::size_t) {}
inline std::size_t getMemoryLimit() { return 0; }
inline void installSignalHandler() {}
#endif

class Limiter: public carl::Singleton<Limiter> {
private:
	std::size_t mMemout;
	std::size_t mTimeout;
	std::size_t mOriginalMemout;
	std::size_t mOriginalTimeout;
public:
	void initialize() {
		installSignalHandler();
		mMemout = 0;
		mTimeout = 0;
		mOriginalMemout = getMemoryLimit();
		mOriginalTimeout = getCPULimit();
	}
	void reset() {
		if (mMemout != 0) {
			mMemout = 0;
			setMemoryLimit(mOriginalMemout);
		}
		if (mTimeout != 0) {
			mTimeout = 0;
			setCPULimit(mOriginalTimeout);
		}
	}
	void setMemout(std::size_t megabytes) {
		mMemout = megabytes;
		setMemoryLimit(mMemout);
	}
	void setTimeout(std::size_t seconds) {
		mTimeout = seconds;
		setCPULimit(usedCPU() + mTimeout);
	}
	void resetTimeout() const {
		if (mTimeout != 0) {
			setCPULimit(usedCPU() + mTimeout);
		}
	}
};

}
}
