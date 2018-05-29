/* 
 * @file delta.cpp
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#include <chrono>
#include <csignal>
#include <fstream>
#include <iostream>

#include "Producer.h"
#include "Parser.h"
#include "Settings.h"
#include "Consumer.h"

#include "../cli/config.h"

#ifndef __WIN
#include <sys/resource.h>
#endif

namespace bpo = boost::program_options;
typedef std::chrono::system_clock Clock;
typedef std::chrono::seconds seconds;

const delta::Producer* producerPtr = nullptr;

void handle_SIGINT(int) {
	if (producerPtr != nullptr) {
		producerPtr->interrupt();
		std::cout << std::endl << "Stopping after this iteration." << std::endl << std::endl;
	}
}

int main(int argc, char* argv[]) {
#ifdef __WIN
    //TODO: do not use magical number
#pragma comment(linker, "/STACK:10000000")
#else
	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);
#endif
	std::signal(SIGINT, &handle_SIGINT);
	auto start = Clock::now();
	
	// Load settings.
	delta::Settings s(argv[0]);
	if (!s.load(argc, argv)) return 1;
	std::string input = s.as<std::string>("input-file");

	// Parse file.
	delta::Node n;
	if (!delta::Parser::parse(input, n)) return 1;
	std::size_t originalSize = n.complexity();

	// Initialize checker.
	std::cout << "Calculating original exit code..." << std::endl;
	auto start_exit = Clock::now();
	delta::Checker c(s.as<std::string>("solver"), s.as<std::size_t>("memout"), s.as<std::size_t>("timeout"), input);
	std::cout << BGREEN << "Original exit code is " << c.expectedCode() << END << std::endl;
	std::size_t duration = (std::size_t)std::chrono::duration_cast<seconds>(Clock::now() - start_exit).count(); 
	std::size_t candidate = (duration + 1) * 2;
	if (s.isDefault("timeout") && (candidate < s.as<std::size_t>("timeout"))) {
		s.set("timeout", candidate);
		c.resetTimeout(candidate);
		std::cout << "Calculation took " << duration << " seconds, the default timeout is set to " << s.as<std::size_t>("timeout") << " seconds." << std::endl;
	} else {
		std::cout << "Calculation took " << duration << " seconds, the configured timeout is " << s.as<std::size_t>("timeout") << " seconds." << std::endl;
	}
	if (c.expectedCode() == 137) {
		std::cout << BRED << "This exit code might be a timeout!" << END << std::endl;
	}
	if (s.has("verbose")) {
		std::cout << "Original (" << n.complexity() << " nodes):" << std::endl << n << std::endl;
	}

	// Perform simplications.
	delta::Producer producer(c, s);
	producerPtr = &producer;
	std::size_t iterations = producer(n);
	if (s.as<bool>("delay-declare-fun")) {
		n.eliminateDefineFuns();
	}
	if (c.getKilled() > 0) {
		std::cout << std::endl << c.getKilled() << " runs during the last iterations have been killed." << std::endl;
		std::cout << std::endl << "This may be due to a timeout." << std::endl;
	}

	// Print result and store to file.
	if (s.has("verbose")) {
		std::cout << std::endl << "Result (" << n.complexity() << " nodes):" << std::endl << n << std::endl;
	} else {
		std::cout << std::endl << "Reduced from " << originalSize << " to " << n.complexity() << " nodes." << std::endl;
	}
	std::string output = s.as<std::string>("output-file");
	std::cout << "Writing to " << output << std::endl;
	std::ofstream out(output);
	out << delta::NodePrinter<true>(n);
	out.close();

	std::cout << "This run took " << std::chrono::duration_cast<seconds>(Clock::now() - start).count() << " seconds for " << iterations << " iterations." << std::endl;
	return 0;
}
