/**
 * @file Node.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <iostream>

namespace rewriter {

class Node {
	std::string id;
public:
	Node() {}
	Node(const std::string& s): id(s) {}
	
	friend std::ostream& operator<<(std::ostream& os, const Node& n);
};

std::ostream& operator<<(std::ostream& os, const Node& n) {
	os << n.id << std::endl;
	return os;
}

}

namespace std {
template<typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v) {
	os << "[";
	for (const auto& t: v) os << t << ", ";
	return os << "]";
}
}