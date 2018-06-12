
cmake_minimum_required (VERSION 3.2 FATAL_ERROR)

include(${CARL_DIR}/../cmake/carlmacros.cmake)

set_version(0 1)

message(STATUS "In ${CARL_DIR}")
message(STATUS "Got ${PROJECT_VERSION_CMAKE}")

file(WRITE ${DEST_FILE} "set(CARL_REQUIRED_VERSION \"${PROJECT_VERSION_CMAKE}\")")

message(STATUS "Stored ${PROJECT_VERSION_CMAKE} as required version.")
