/**
 * @file logging.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "config.h"

#if defined LOGGING
	#include <carl/core/carlLogging.h>
	#define SMTRAT_LOG_FATAL(channel, msg) __CARL_LOG_FATAL(channel, msg)
	#define SMTRAT_LOG_ERROR(channel, msg) __CARL_LOG_ERROR(channel, msg)
	#define SMTRAT_LOG_WARN(channel, msg) __CARL_LOG_WARN(channel, msg)
	#define SMTRAT_LOG_INFO(channel, msg) __CARL_LOG_INFO(channel, msg)
	#define SMTRAT_LOG_DEBUG(channel, msg) __CARL_LOG_DEBUG(channel, msg)	
	#define SMTRAT_LOG_TRACE(channel, msg) __CARL_LOG_TRACE(channel, msg)

	#define SMTRAT_LOG_FUNC(channel, args) __CARL_LOG_FUNC(channel, args)
	#define SMTRAT_LOG_ASSERT(channel, condition, msg) __CARL_LOG_ASSERT(channel, condition, msg)
	#define SMTRAT_LOG_NOTIMPLEMENTED() __CARL_LOG_ERROR("", "Not implemented method-stub called.")
	#define SMTRAT_LOG_INEFFICIENT() __CARL_LOG_WARN("", "Inefficient method called.")
#else
	#define SMTRAT_LOG_FATAL(channel, msg) std::cerr << "FATAL " << channel << ": " << msg << std::endl;
	#define SMTRAT_LOG_ERROR(channel, msg) std::cerr << "ERROR " << channel << ": " << msg << std::endl;
	#define SMTRAT_LOG_WARN(channel, msg) {}
	#define SMTRAT_LOG_INFO(channel, msg) {}
	#define SMTRAT_LOG_DEBUG(channel, msg) {}
	#define SMTRAT_LOG_TRACE(channel, msg) {}

	#define SMTRAT_LOG_FUNC(channel, args)
	#define SMTRAT_LOG_ASSERT(channel, condition, msg) assert(condition)
	#define SMTRAT_LOG_NOTIMPLEMENTED()
	#define SMTRAT_LOG_INEFFICIENT()
#endif
