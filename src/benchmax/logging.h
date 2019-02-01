/**
 * @file logging.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <carl/core/carlLogging.h>

namespace benchmax {
using carl::operator<<;

/**
 * Configure default logging for benchmax.
 */
inline void logging_configure() {
	carl::logging::logger().configure("stdout", std::cout);
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_INFO)
	;
	carl::logging::logger().resetFormatter();
}

/**
 * Configure quiet logging for benchmax.
 */
inline void logging_quiet() {
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_WARN)
	;
}

/**
 * Configure verbose logging for benchmax.
 */
inline void logging_verbose() {
	carl::logging::logger().filter("stdout")
		("benchmax", carl::logging::LogLevel::LVL_DEBUG)
	;
}

}

#define BENCHMAX_LOG_FATAL(channel, msg) __CARL_LOG_FATAL(channel, msg)
#define BENCHMAX_LOG_ERROR(channel, msg) __CARL_LOG_ERROR(channel, msg)
#define BENCHMAX_LOG_WARN(channel, msg) __CARL_LOG_WARN(channel, msg)
#define BENCHMAX_LOG_INFO(channel, msg) __CARL_LOG_INFO(channel, msg)
#define BENCHMAX_LOG_DEBUG(channel, msg) __CARL_LOG_DEBUG(channel, msg)	
#define BENCHMAX_LOG_TRACE(channel, msg) __CARL_LOG_TRACE(channel, msg)

#define BENCHMAX_LOG_FUNC(channel, args) __CARL_LOG_FUNC(channel, args)
#define BENCHMAX_LOG_ASSERT(channel, condition, msg) __CARL_LOG_ASSERT(channel, condition, msg)
#define BENCHMAX_LOG_NOTIMPLEMENTED() __CARL_LOG_ERROR("", "Not implemented method-stub called.")
#define BENCHMAX_LOG_INEFFICIENT() __CARL_LOG_WARN("", "Inefficient method called.")

