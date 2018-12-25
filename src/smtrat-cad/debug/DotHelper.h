#pragma once

#include <iostream>
#include <vector>

namespace smtrat {
namespace cad {
namespace debug {

struct DotSubgraph {
	std::string name;
	std::vector<std::string> nodes;
	DotSubgraph(const std::string& n): name(n) {}
	void add(const std::string& n) {
		nodes.push_back(n);
	}
	friend std::ostream& operator<<(std::ostream& os, const DotSubgraph& dsg) {
		os << "subgraph " << dsg.name << " { rank = same; ";
		for (const auto& n: dsg.nodes) {
			os << n << "; ";
		}
		return os << "}";
	}
};

}
}
}
