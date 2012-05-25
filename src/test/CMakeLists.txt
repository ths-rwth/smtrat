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
# Version: 2012-03-21                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( "${PROJECT_SOURCE_DIR}/src" )
link_directories( "${PROJECT_BINARY_DIR}/src" )

set(check_SOURCES test.cpp
	CSDP_unittest.cpp CSDP_unittest.h 
	GroebnerToSDP_unittest.cpp GroebnerToSDP_unittest.h
	ConstraintMatrixFactory_unittest.cpp ConstraintMatrixFactory_unittest.h
	DenseMatrix_unittest.cpp DenseMatrix_unittest.h

)

add_executable(check_${PROJECT_NAME} ${check_SOURCES})

# executable target
add_custom_target( check
                   COMMAND check_${PROJECT_NAME}
                   DEPENDS check_${PROJECT_NAME}
                   COMMENT "${${PROJECT_NAME}_NAME} ${${PROJECT_NAME}_VERSION} CPPUnit Test Suite" )

# link the libraries
target_link_libraries( check_${PROJECT_NAME}
                       ${CPPUNIT_LIBRARIES}
					 ${cln_LIBRARIES} ${GINAC_LIBRARY} ${GINACRA_LIBRARY} 
                       ${PROJECT_NAME} )


