# Options
option(BENCHMAX_DATABASE "Enable database storage for results." OFF)
option(BENCHMAX_SSH "Enable SSH backend." ON)

# Benchmax binary
include_directories(${CMAKE_SOURCE_DIR}/src)
file(GLOB_RECURSE benchmax_sources "*.cpp")
add_executable( benchmax ${benchmax_sources})
target_link_libraries(benchmax stdc++fs pthread carl-arith-shared carl-settings-shared ${Boost_SHARED} Boost_serialization_SHARED)

# Database
if(BENCHMAX_DATABASE)
	find_library(LIBMYSQL NAMES libmysqlclient)
	target_link_libraries(benchmax ${LIBMYSQL} mysqlcppconn)
endif()

# SSH
if(BENCHMAX_SSH)
	find_library(LIBSSH NAMES ssh)
	find_library(LIBSSHTHREADS NAMES ssh_threads)
	if(LIBSSH)
		target_link_libraries(benchmax ${LIBSSH})
	else()
		message(STATUS "Did not find libssh, disabled SSH backend.")
		set(BENCHMAX_SSH OFF)
	endif()

	if(LIBSSHTHREADS)
		target_link_libraries(benchmax ${LIBSSHTHREADS})
	else()
		message(STATUS "Did not find libssh_threads. If you have a libssh version < 0.8, then this is an error. Beginning from 0.8, libssh_threads is not required.")
	endif()
else()
	message(STATUS "SSH backend disabled.")
endif()

# Config file
configure_file(${CMAKE_SOURCE_DIR}/src/benchmax/config.h.in ${CMAKE_SOURCE_DIR}/src/benchmax/config.h)
