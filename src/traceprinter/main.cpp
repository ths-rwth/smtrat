#include <iostream>

#include "Parser.h"

int main(int argc, char* argv[]) {
	assert(argc > 1);
	std::vector<rewriter::Node> res;
	if (rewriter::Parser::parse(argv[1], res)) {
		for (const auto& n: res) {
			std::cout << n << std::endl;
		}
	} else {
		std::cout << "Parsing failed" << std::endl;
	}
}
