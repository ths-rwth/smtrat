option(BENCHMAX_USE_SMTPARSER "Use parser for smtlib files." OFF)
option(BENCHMAX_LOGGING "Use logging in benchmax. Strongly encouraged!" ON)
option(BENCHMAX_DATABASE "Store results in a database." OFF)

configure_file(${CMAKE_SOURCE_DIR}/src/benchmax/config.h.in ${CMAKE_SOURCE_DIR}/src/benchmax/config.h)

file(GLOB_RECURSE benchmax_sources "*.cpp")
add_executable( benchmax ${benchmax_sources})
target_link_libraries(benchmax pthread lib_carl)

find_package(Boost 1.55 REQUIRED COMPONENTS chrono filesystem program_options system)
if(Boost_FOUND)
	target_link_libraries(benchmax ${Boost_LIBRARIES})
endif()

if(BENCHMAX_DATABASE)
	find_library(LIBMYSQL NAMES libmysqlclient)
	target_link_libraries(benchmax ${LIBMYSQL} mysqlcppconn)
endif()

find_library(LIBSSH NAMES ssh)
find_library(LIBSSH_THREADS NAMES ssh_threads)
if(LIBSSH AND LIBSSH_THREADS)
	target_link_libraries(benchmax ${LIBSSH} ${LIBSSH_THREADS})
endif()
