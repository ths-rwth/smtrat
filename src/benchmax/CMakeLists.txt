option( BENCHMAX_USE_SMTPARSER "Use parser for smtlib files." OFF )
option( BENCHMAX_LOGGING "Use logging in benchmax. Strongly encouraged!" ON )
option( BENCHMAX_DATABASE "Store results in a database." OFF )

configure_file( ${CMAKE_SOURCE_DIR}/src/benchmax/config.h.in ${CMAKE_SOURCE_DIR}/src/benchmax/config.h )

add_subdirectory(backends)
add_subdirectory(tools)

add_executable( benchmax benchmax.cpp BenchmarkSet.h BenchmarkSet.cpp Stats.cpp
			Settings.cpp BenchmarkStatus.cpp ${backends_sources} ${ssh_sources} ${tool_sources})
include_directories(${carl_INCLUDE_DIR})

set(DYNAMIC_EXT "so")
set(STATIC_EXT "a")
if(APPLE)
	set(DYNAMIC_EXT "dylib")
	set(STATIC_EXT "a")
endif()
message("-- Assuming extension for shared libraries: .${DYNAMIC_EXT}")
message("-- Assuming extension for static libraries: .${STATIC_EXT}")

find_library(ALIBBCH NAMES libboost_chrono.${STATIC_EXT})
find_library(SLIBBCH NAMES libboost_chrono.${DYNAMIC_EXT})
find_library(ALIBBFS NAMES libboost_filesystem.${STATIC_EXT})
find_library(SLIBBFS NAMES libboost_filesystem.${DYNAMIC_EXT})
find_library(ALIBBPO NAMES libboost_program_options.${STATIC_EXT})
find_library(SLIBBPO NAMES libboost_program_options.${DYNAMIC_EXT})
find_library(ALIBBSY NAMES libboost_system.${STATIC_EXT})
find_library(SLIBBSY NAMES libboost_system.${DYNAMIC_EXT})
if(BENCHMAX_DATABASE)
find_library(ALIBMYSQL NAMES libmysqlclient.${DYNAMIC_EXT})
find_library(SLIBMYSQL NAMES libmysqlclient.${DYNAMIC_EXT})
endif()
find_library(ALIBSSH NAMES libssh.${STATIC_EXT})
find_library(SLIBSSH NAMES libssh.${DYNAMIC_EXT})



if(${STATICLIB_SWITCH} STREQUAL "ON")
	set(LIBS ${ALIBBCH} ${ALIBBFS} ${ALIBBPO} ${ALIBBSY} ${ALIBMYSQL} ${ALIBSSH})
	target_link_libraries( benchmax ${LIBS} ssl crypto dl z pthread ${libraries} ssh_threads)
else()
	set(LIBS ${SLIBBCH} ${SLIBBFS} ${SLIBBPO} ${SLIBBSY} ${SLIBMYSQL} ${SLIBSSH})
	target_link_libraries( benchmax ${LIBS} mysqlcppconn pthread ${libraries} ssh_threads)
endif()

# stripping
add_custom_target( strip-unneeded strip --strip-unneeded benchmax DEPENDS benchmax WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR} COMMENT "Stripping unneeded symbols" )
if(${CMAKE_BUILD_TYPE} STREQUAL "Release")
    add_custom_target( strip-debug ALL strip --strip-debug benchmax DEPENDS benchmax WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR} COMMENT "Stripping unneeded symbols" )
endif()

add_custom_target( benchmax_move mv -v ${CMAKE_CURRENT_BINARY_DIR}/benchmax ${CMAKE_BINARY_DIR}/
                   DEPENDS benchmax
                   COMMENT "Moving binary to ${CMAKE_BINARY_DIR}" )
