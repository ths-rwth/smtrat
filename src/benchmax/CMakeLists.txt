# Options
option(BENCHMAX_DATABASE "Enable database storage for results." OFF)
option(BENCHMAX_SSH "Enable SSH backend." ON)

# Benchmax binary
include_directories(${CMAKE_SOURCE_DIR}/src)
file(GLOB_RECURSE benchmax_sources "*.cpp")
add_executable( benchmax ${benchmax_sources})
target_link_libraries(benchmax stdc++fs pthread carl-shared ${Boost_SHARED})

# Database
if(BENCHMAX_DATABASE)
	find_library(LIBMYSQL NAMES libmysqlclient)
	target_link_libraries(benchmax ${LIBMYSQL} mysqlcppconn)
endif()

# SSH
if(BENCHMAX_SSH)
	find_library(LIBSSH NAMES ssh)
	if(LIBSSH)
		target_link_libraries(benchmax ${LIBSSH})
	else()
		message(STATUS "Did not find libssh, disabled SSH backend.")
		set(BENCHMAX_SSH OFF)
	endif()
else()
	message(STATUS "SSH backend disabled.")
endif()

# Doxygen
get_target_property(DOXYGEN_BIN Doxygen::doxygen IMPORTED_LOCATION)

configure_file(doc/doxygen.conf.in ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf)

add_custom_target(benchmax-doc
	Doxygen::doxygen ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf
	DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf Doxygen::doxygen doxygen-build
)

# Config file
configure_file(${CMAKE_SOURCE_DIR}/src/benchmax/config.h.in ${CMAKE_SOURCE_DIR}/src/benchmax/config.h)
