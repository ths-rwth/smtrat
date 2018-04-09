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

#include_directories( ${PROJECT_SOURCE_DIR}/src )
#link_directories( ${PROJECT_BINARY_DIR}/src
#                  ${PROJECT_BINARY_DIR} )


#add_executable( check_${PROJECT_NAME} test.cpp )

# executable target
#add_custom_target( check
#                   COMMAND check_${PROJECT_NAME}
#                   DEPENDS check_${PROJECT_NAME}
#                   COMMENT "${${PROJECT_NAME}_NAME} ${${PROJECT_NAME}_VERSION} CPPUnit Test Suite"
#)

# link the libraries
#target_link_libraries( check_${PROJECT_NAME}
#                       ${CPPUNIT_LIBRARIES}
#                       ${PROJECT_NAME}
#                       ${libraries}
#)

#set_target_properties( check_${PROJECT_NAME} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

add_executable( parserTest
	ParserTest.cpp
)

set_target_properties( parserTest PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

include_directories(${CMAKE_SOURCE_DIR}/src
                    ${CMAKE_SOURCE_DIR}/src/cli
                    ${CMAKE_BINARY_DIR}/src/cli
                    ${carl_INCLUDE_DIR}
 )
target_link_libraries( parserTest
                        lib_${PROJECT_NAME} # smtrat library
                        ${libraries} # libraries definied in top-level CMakeLists.txt
)

add_subdirectory(cad)
add_subdirectory(onecellcad)
add_subdirectory(datastructures)
add_subdirectory(nlsat)
