/**
 * @file Manager.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <algorithm>
#include <iostream>
#include <sstream>
#include <vector>

#include "operators.h"
#include "utils.h"
#include "Settings.h"
#include "Checker.h"
#include "Consumer.h"

namespace delta {

/**
 * This class iteratively applies the operators to a smtlib file until no further simplifications can be performed.
 */
class Producer {
	/// Registered operators.
	std::vector<std::tuple<NodeOperator, std::string, std::string, std::string>> operators;
	// Executor object.
	Consumer consumer;
	/// Progress.
	ProgressBar progress;
	/// Settings.
	Settings settings;
	/// Verbose flag.
	bool verbose;
	bool delayDeclareFun;
	/// Interrupt flat.
	mutable bool interrupted;
public:
	/**
	 * Create a new manager that uses the given checker.
	 * @param checker Checker to call the solver.
	 * @param settings Settings object.
	 */
	Producer(const Checker& checker, const Settings& settings):
		consumer(settings.as<std::string>("temp-file"), settings.as<std::size_t>("threads"), checker), settings(settings), interrupted(false)
	{
		if (!settings.has("no-constants")) operators.emplace_back(&constant, "Replaced variable ", " by constant ", ".");
		if (!settings.has("no-children")) operators.emplace_back(&children, "Replaced ", " by child ", ".");
		if (!settings.has("no-reorder")) operators.emplace_back(&reorderChildren, "Reordered children of ", " to ", ".");
		if (!settings.has("no-merge")) operators.emplace_back(&mergeChild, "Merged ", " with child ", ".");
		if (!settings.has("no-numbers")) operators.emplace_back(&number, "Replaced number ", " by ", ".");
		if (!settings.has("no-lets")) operators.emplace_back(&letExpression, "Eliminated ", " by ", ".");
		operators.emplace_back(&BV_zeroExtend, "Eliminated zero_extend ", " by ", ".");
		operators.emplace_back(&BV_mergeShift, "Merged ", " with ", ".");
		verbose = settings.has("verbose");
		delayDeclareFun = settings.as<bool>("delay-declare-fun");
	}

	void interrupt() const {
		interrupted = true;
	}
	
	/**
	 * Apply simplifications to the given node.
	 * @param root Node to simplify.
	 */
	std::size_t operator()(Node& root) {
		std::size_t skip = 0;
		if (settings.has("skip")) skip = settings.as<std::size_t>("skip");
		for (std::size_t i = 1; ; i++) {
			consumer.reset();
			progress(0, root.complexity());
			std::size_t num = 0;
			if (skip > 0) skip--;
			if (settings.has("useDFS")) dfs(root, &root, num, skip);
			else bfs(root, num, skip);
			if (verbose) {
				std::cout << GRAY << "Waiting for processes to terminate..." << END << std::endl << std::endl;
				while (!consumer.wait()) progress(consumer.getProgress());
				progress(consumer.getProgress());
			} else {
				while (!consumer.wait());
			}
			if (consumer.hasResult()) {
				auto r = consumer.getResult();
				root = std::get<0>(r);
				skip = std::get<2>(r); // skip until this node
				std::cout << GREEN << "Success: " << std::get<1>(r) << END << std::endl;
				std::ofstream out("delta.last.smt2");
				out << root;
				out.close();
			} else if (skip > 0) {
				skip = 0;
				std::cout << BGREEN << "Finished successful iteration, starting over." << END << std::endl << std::endl;
				std::ofstream out("delta.last.smt2");
				out << root;
				out.close();
			} else {
				std::cout << std::endl << BRED << "No further simplifications found." << END << std::endl;
				return i;
			}
			if (interrupted) {
				std::cout << std::endl << "Terminating due to interruption." << std::endl;
				return i;
			}
		}
	}
private:
	/**
	 * Iterate over nodes using DFS.
	 * @param root Root of nodes.
	 * @param n Current node.
	 * @param num Internal counter of node.
	 * @param skip Number of nodes to skip.
	 */
	void dfs(const Node& root, const Node* n, std::size_t& num, std::size_t skip) {
		if (consumer.hasResult()) return;
		progress();
		if (skip < num) process(root, *n, num);
		num++;
		for (const auto& child: n->children) {
			if (child.immutable()) continue;
			dfs(root, &child, num, skip);
		}
	}
	/**
	 * Iterate over nodes using BFS.
	 * @param root Root of nodes.
	 * @param num Internal counter of node.
	 * @param skip Number of nodes to skip.
	 */
	void bfs(const Node& root, std::size_t& num, std::size_t skip) {
		std::queue<const Node*> q;
		q.push(&root);
		while (!q.empty()) {
			if (consumer.hasResult()) return;
			progress();
			if (skip < num) process(root, *q.front(), num);
			num++;
			for (const auto& child: q.front()->children) {
				if (child.immutable()) {
					progress(child.complexity());
					continue;
				}
				q.push(&child);
			}
			q.pop();
		}
	}
	
	/**
	 * Performs the actual simplifications.
	 * @param root Root of the current smtlib file.
	 * @param n Node that is currently processed.
	 * @param num Current progress.
	 */
	void process(const Node& root, const Node& n, std::size_t num) {
		if (n.immutable()) return;
		if (&root == &n) return;
		if (delayDeclareFun) {
			if (n.name == "declare-fun") return;
		}
		if (!settings.has("no-removal")) {
			consumer.consume(root.clone(&n, nullptr), String() << "Removed \"" << n.repr(verbose) << "\"", num);
		}
		for (const auto& op: operators) {
			auto changes = std::get<0>(op)(n);
			for (const auto& c: changes) {
				consumer.consume(root.clone(&n, &c), String() << std::get<1>(op) << "\"" << n.repr(verbose) << "\"" << std::get<2>(op) << "\"" << c.repr(verbose) << "\"" << std::get<3>(op), num);
			}
		}
	}
};

}
