/**
 * @file Manager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <sstream>
#include <vector>

#include "../lib/Common.h"

#include "operators.h"
#include "Checker.h"

namespace delta {

/**
 * This class iteratively applies the operators to a smtlib file until no further simplifications can be performed.
 */
class Manager {
	/// Registered operators.
	std::vector<std::tuple<NodeOperator, std::string, std::string, std::string>> operators;
	/// Checker object.
	Checker checker;
	/// Verbosity flag.
	bool verbose;
	
	/// Terminal code for red font.
	std::string red = "\033[1;31m";
	/// Terminal code for green font.
	std::string green = "\033[1;32m";
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
public:
	/**
	 * Create a new manager that uses the given checker.
	 * @param checker Checker to call the solver.
	 * @param verbose Verbosity flag.
	 */
	Manager(const Checker& checker, bool verbose): checker(checker), verbose(verbose) {
		operators.emplace_back(&children, "Replaced ", " by child ", ".");
		operators.emplace_back(&number, "Replaced ", " by number ", ".");
	}
	
	/**
	 * Apply simplifications to the given node.
	 * @param n Node to simplify.
	 */
	void simplify(Node& n) {
		unsigned progress = 0;
		bool res = process(n, n, progress);
		while(res) {
			std::cout << std::endl << green << "Simplified problem, starting over." << end << std::endl;
			progress = 0;
			progressbar(progress, n.complexity());
			res = process(n, n, progress);
		}
		std::cout << std::endl << red << "No further simplifications found." << end << std::endl;
	}
	
private:
	/**
	 * Recursive method that performs the actual simplifications.
	 * @param root Root of the current smtlib file.
	 * @param n Node that is currently processed.
	 * @param progress Current progress.
	 */
	bool process(Node& root, Node& n, unsigned& progress) {
		progressbar(++progress, root.complexity());
		for (auto it = n.children.begin(); it != n.children.end(); it++) {
			if (!it->removable()) continue;
			Node tmp = *it;
			it = n.children.erase(it);
			if (checker(root)) {
				if (verbose) std::cout << "Removed " << tmp << std::endl;
				else std::cout << "Removed " << tmp.shortName() << std::endl;
				return true;
			}
			it = n.children.insert(it, tmp);
		}
		for (auto& child: n.children) {
			for (auto op: operators) {
				auto changes = std::get<0>(op)(child);
				for (auto& c: changes) {
					std::swap(child, c);
					if (checker(root)) {
						if (verbose) std::cout << std::get<1>(op) << c << std::get<2>(op) << child << std::get<3>(op) << std::endl;
						else std::cout << std::get<1>(op) << c.shortName() << std::get<2>(op) << child.shortName() << std::get<3>(op) << std::endl;
						return true;
					}
					std::swap(child, c);
				}
			}
		}
		for (auto& child: n.children) {
			if (process(root, child, progress)) return true;
		}
		return false;
	}
};

}