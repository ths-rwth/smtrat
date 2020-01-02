option(CLANG_TIME_TRACE "Enable clang profiling." OFF)

if(CLANG_TIME_TRACE)
	set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -ftime-trace")
endif()