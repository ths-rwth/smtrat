#pragma once

#include <chrono>

namespace benchmax {

template<typename D>
inline std::chrono::seconds seconds(const D& d) {
	return std::chrono::duration_cast<std::chrono::seconds>(d);
}
template<typename D>
inline std::chrono::milliseconds milliseconds(const D& d) {
	return std::chrono::duration_cast<std::chrono::milliseconds>(d);
}
	
}
