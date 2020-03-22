## Logging {#logging}

### Logging frontend

The frontend for logging is defined in [logging.h](@ref logging.h).

It provides the following macros for logging:
- SMTRAT_LOG_TRACE(channel, msg)
- SMTRAT_LOG_DEBUG(channel, msg)
- SMTRAT_LOG_INFO(channel, msg)
- SMTRAT_LOG_WARN(channel, msg)
- SMTRAT_LOG_ERROR(channel, msg)
- SMTRAT_LOG_FATAL(channel, msg)
- SMTRAT_LOG_FUNC(channel, args)
- SMTRAT_LOG_FUNC(channel, args, msg)
- SMTRAT_LOG_ASSERT(channel, condition, msg)
- SMTRAT_LOG_NOTIMPLEMENTED()
- SMTRAT_LOG_INEFFICIENT()

Where the arguments mean the following:
- `channel`: A string describing the context. For example `"smtrat.parser"`.
- `msg`: The actual message as an expression that can be sent to a std::stringstream. For example `"foo: " << foo`.
- `args`: A description of the function arguments as an expression like `msg`.
- `condition`: A boolean expression that can be passed to `assert()`.

Typically, logging looks like this:

	bool checkStuff(Object o, bool flag) {
		SMTRAT_LOG_FUNC("smtrat", o << ", " << flag);
		bool result = o.property(flag);
		SMTRAT_LOG_TRACE("smtrat", "Result: " << result);
		return result;
	}

Logging is enabled (or disabled) by the `LOGGING` macro in CMake.
