/**
 * @file Manager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <iostream>
#include <sstream>
#include <vector>

#include "../lib/Common.h"

#include "operators.h"
#include "Checker.h"
#include "Executor.h"

namespace delta {

/**
 * This class iteratively applies the operators to a smtlib file until no further simplifications can be performed.
 */
class Manager {
	/// Registered operators.
	std::vector<std::tuple<NodeOperator, std::string, std::string, std::string>> operators;
	/// Checker object.
	Checker checker;
	// Executor object.
	Executor executor;
	/// Verbosity flag.
	bool verbose;
	
	/// Terminal code for bold red font.
	std::string bred = "\033[1;31m";
	/// Terminal code for bold green font.
	std::string bgreen = "\033[1;32m";
	/// Terminal code for green font.
	std::string green = "\033[0;32m";
	/// Terminal code for gray font.
	std::string gray = "\033[0;37m";
	/// Terminal code for default font.
	std::string end = "\033[0;39m";
	/// Terminal code to remove the previous line.
	std::string clearline = "\033[1F\033[1K";
	/**
	 * Print a progress bar for a progress of `n / total`.
	 * @param n Processed items.
	 * @param total Items to be processed.
	 */
	void progressbar(unsigned n, unsigned total) {
		unsigned size = n*30 / total;
		if (size == ((n-1)*30 / total)) return;
		if (n > 0) std::cout << clearline;
		std::cout << "[" << std::string(size, '=') << std::string(30 - size, ' ') << "] (" << n << " / " << total << ")" << std::endl;
	}
	/**
	 * Print a progress bar for a progress of `n / total`.
     * @param p Pair of `n` and `total`.
     */
	void progressbar(const std::pair<unsigned, unsigned>& p) {
		progressbar(p.first, p.second);
	}
public:
	/**
	 * Create a new manager that uses the given checker.
	 * @param checker Checker to call the solver.
	 * @param verbose Verbosity flag.
	 */
	Manager(const Checker& checker, const std::string& temp, bool verbose):
		checker(checker), executor(temp), verbose(verbose)
	{
		operators.emplace_back(&children, "Replaced ", " by child ", ".");
		operators.emplace_back(&number, "Replaced ", " by number ", ".");
	}
	
	/**
	 * Apply simplifications to the given node.
	 * @param n Node to simplify.
	 */
	void simplify(Node& n) {
		executor.reset();
		while (true) {
			unsigned progress = 0;
			progressbar(progress, n.complexity());
			process(n, n, progress);
			std::cout << gray << "Waiting for processes to terminate..." << end << std::endl << std::endl;
			while (!executor.wait()) progressbar(executor.getProgress());
			progressbar(executor.getProgress());
			if (executor.hasResult()) {
				auto r = executor.getResult();
				n = r.first;
				std::cout << green << "Success: " << r.second << end << std::endl;
				std::cout << std::endl << bgreen << "Simplified problem, starting over." << end << std::endl;
			} else {
				break;
			}
			executor.reset();
		}
		std::cout << std::endl << bred << "No further simplifications found." << end << std::endl;
	}
	
private:
	/**
	 * Recursive method that performs the actual simplifications.
	 * @param root Root of the current smtlib file.
	 * @param n Node that is currently processed.
	 * @param progress Current progress.
	 */
	void process(const Node& root, Node& n, unsigned& progress) {
		if (executor.hasResult()) return;
		progressbar(++progress, root.complexity());
		if (!n.removable()) return;
		for (auto it = n.children.begin(); it != n.children.end(); it++) {
			if (!it->removable()) continue;
			Node tmp = *it;
			it = n.children.erase(it);
			std::stringstream ss;
			if (verbose) ss << "Removed " << tmp;
			else ss << "Removed " << tmp.shortName();
			executor.check(root, checker, ss.str());
			it = n.children.insert(it, tmp);
		}
		for (auto& child: n.children) {
			for (auto op: operators) {
				auto changes = std::get<0>(op)(child);
				for (auto& c: changes) {
					std::swap(child, c);
					std::stringstream ss;
					if (verbose) ss << std::get<1>(op) << c << std::get<2>(op) << child << std::get<3>(op);
					else ss << std::get<1>(op) << c.shortName() << std::get<2>(op) << child.shortName() << std::get<3>(op);
					executor.check(root, checker, ss.str());
					std::swap(child, c);
				}
			}
		}
		for (auto& child: n.children) {
			process(root, child, progress);
		}
	}
};

}