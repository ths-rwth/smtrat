# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-07-30                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( ${PROJECT_SOURCE_DIR}/src )
link_directories( ${PROJECT_BINARY_DIR}/src
                  ${PROJECT_BINARY_DIR} )


add_executable( check_${PROJECT_NAME} test.cpp )

# executable target
add_custom_target( check
                   COMMAND check_${PROJECT_NAME}
                   DEPENDS check_${PROJECT_NAME}
                   COMMENT "${${PROJECT_NAME}_NAME} ${${PROJECT_NAME}_VERSION} CPPUnit Test Suite"
)

# link the libraries
target_link_libraries( check_${PROJECT_NAME}
                       ${CPPUNIT_LIBRARIES}
                       ${PROJECT_NAME}
                       ${libraries}
)

set_target_properties( check_${PROJECT_NAME} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )
