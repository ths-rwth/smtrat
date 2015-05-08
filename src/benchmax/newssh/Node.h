#pragma once

namespace benchmax {
namespace ssh {
	
	struct Node {
		std::string hostname;
		std::string username;
		std::string password;
		int port;
		unsigned long cores;
		std::size_t connections;
	};
	
}
}
