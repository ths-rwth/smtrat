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
# Version: 2013-04-18                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


add_subdirectory(lib)
if(BUILD_SOLVER)
	add_subdirectory(cli)
endif()
# unit tests
# # # # # # #

add_subdirectory(benchmax EXCLUDE_FROM_ALL)

add_subdirectory(tests EXCLUDE_FROM_ALL)

add_subdirectory(gui EXCLUDE_FROM_ALL)

add_subdirectory(delta)
