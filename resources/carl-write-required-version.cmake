
cmake_minimum_required (VERSION 3.2 FATAL_ERROR)

include(${CARL_DIR}/../cmake/carlmacros.cmake)

set_version(0 1)

file(WRITE ${DEST_FILE} "${PROJECT_VERSION}")

message(STATUS "Stored ${PROJECT_VERSION} as required version.")
