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
public:
	/**
	 * Create a new manager that uses the given checker.
	 * @param checker Checker to call the solver.
	 * @param settings Settings object.
	 */
	Producer(const Checker& checker, const Settings& settings):
		consumer(settings.as<std::string>("temp-file"), checker), settings(settings)
	{
		if (!settings.has("no-constants")) operators.emplace_back(&constant, "Replaced variable ", " by constant ", ".");
		if (!settings.has("no-children")) operators.emplace_back(&children, "Replaced ", " by child ", ".");
		if (!settings.has("no-numbers")) operators.emplace_back(&number, "Replaced number ", " by ", ".");
		if (!settings.has("no-lets")) operators.emplace_back(&letExpression, "Eliminated ", " by ", ".");
		verbose = settings.has("verbose");
	}
	
	/**
	 * Apply simplifications to the given node.
	 * @param n Node to simplify.
	 */
	unsigned operator()(Node& root) {
		for (unsigned i = 1; ; i++) {
			consumer.reset();
			progress(0, root.complexity());
			if (settings.has("useDFS")) dfs(root, &root);
			else bfs(root);
			std::cout << GRAY << "Waiting for processes to terminate..." << END << std::endl << std::endl;
			while (!consumer.wait()) progress(consumer.getProgress());
			progress(consumer.getProgress());
			if (consumer.hasResult()) {
				auto r = consumer.getResult();
				root = r.first;
				std::cout << GREEN << "Success: " << r.second << END << std::endl;
				std::cout << std::endl << BGREEN << "Simplified problem, starting over." << END << std::endl;
			} else {
				std::cout << std::endl << BRED << "No further simplifications found." << END << std::endl;
				return i;
			}
		}
	}
private:
	/**
	 * Iterate over nodes using DFS.
	 * @param root Root of nodes.
	 * @param n Current node.
	 */
	void dfs(const Node& root, const Node* n) {
		if (consumer.hasResult()) return;
		progress();
		process(root, n);
		for (const auto& child: n->children) {
			if (child.immutable()) continue;
			dfs(root, &child);
		}
	}
	/**
	 * Iterate over nodes using BFS.
	 * @param root Root of nodes.
	 */
	void bfs(const Node& root) {
		std::queue<const Node*> q;
		q.push(&root);
		while (!q.empty()) {
			if (consumer.hasResult()) return;
			progress();
			process(root, q.front());
			for (const auto& child: q.front()->children) {
				if (child.immutable()) continue;
				q.push(&child);
			}
			q.pop();
		}
	}
	
	/**
	 * Performs the actual simplifications.
	 * @param root Root of the current smtlib file.
	 * @param n Node that is currently processed.
	 * @param progress Current progress.
	 */
	void process(const Node& root, const Node* n) {
		for (auto& child: n->children) {
			if (child.immutable()) continue;
			if (!settings.has("no-removal")) {
				consumer.consume(root.clone(&child, nullptr), String() << "Removed \"" << child.repr(verbose) << "\"");
			}
			for (auto op: operators) {
				auto changes = std::get<0>(op)(child);
				for (auto& c: changes) {
					consumer.consume(root.clone(&child, &c), String() << std::get<1>(op) << "\"" << child.repr(verbose) << "\"" << std::get<2>(op) << "\"" << c.repr(verbose) << "\"" << std::get<3>(op));
				}
			}
		}
	}
};

}