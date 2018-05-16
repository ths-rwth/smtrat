# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-07-30                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

find_package(Boost COMPONENTS unit_test_framework REQUIRED)

add_definitions(-DBOOST_TEST_DYN_LINK)

include_directories(${CMAKE_SOURCE_DIR}/src
                    ${CMAKE_SOURCE_DIR}/src/cli
                    ${CMAKE_BINARY_DIR}/src/cli
                    ${carl_INCLUDE_DIR}
 )

add_subdirectory(cad)
add_subdirectory(parser)
add_subdirectory(pseudobool)
add_subdirectory(onecellcad)
add_subdirectory(datastructures)
add_subdirectory(nlsat)

