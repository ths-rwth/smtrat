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

/// Log fatal errors.
#define BENCHMAX_LOG_FATAL(channel, msg) __CARL_LOG_FATAL(channel, msg)
/// Log errors.
#define BENCHMAX_LOG_ERROR(channel, msg) __CARL_LOG_ERROR(channel, msg)
/// Log warnings.
#define BENCHMAX_LOG_WARN(channel, msg) __CARL_LOG_WARN(channel, msg)
/// Log informational messages.
#define BENCHMAX_LOG_INFO(channel, msg) __CARL_LOG_INFO(channel, msg)
/// Log debug messages.
#define BENCHMAX_LOG_DEBUG(channel, msg) __CARL_LOG_DEBUG(channel, msg)	
/// Log trace messages.
#define BENCHMAX_LOG_TRACE(channel, msg) __CARL_LOG_TRACE(channel, msg)

/// Log function call with function arguments.
#define BENCHMAX_LOG_FUNC(channel, args) __CARL_LOG_FUNC(channel, args)
/// Assert and log an some condition.
#define BENCHMAX_LOG_ASSERT(channel, condition, msg) __CARL_LOG_ASSERT(channel, condition, msg)
/// Warn about some function not being implemented.
#define BENCHMAX_LOG_NOTIMPLEMENTED() __CARL_LOG_ERROR("", "Not implemented method-stub called.")
/// Warn about some function being inefficient.
#define BENCHMAX_LOG_INEFFICIENT() __CARL_LOG_WARN("", "Inefficient method called.")

