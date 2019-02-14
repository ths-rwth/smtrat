#pragma once

namespace benchmax {
namespace ssh {

/// Specification of a compuation node for the SSH backend.
struct Node {
	/// Hostname to connect to.
	std::string hostname;
	/// Username.
	std::string username;
	/// Password (only used if public key authentication fails).
	std::string password;
	/// Port (default is 22)
	int port;
	/// Number of cores we use per connection (default is 1)
	unsigned long cores;
	/// Number of concurrent connections (default is 1)
	std::size_t connections;
};

} // namespace ssh
} // namespace benchmax
