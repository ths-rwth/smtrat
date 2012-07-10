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
# Version: 2012-07-06                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

include_directories( "${PROJECT_SOURCE_DIR}/src" )
link_directories( "${PROJECT_BINARY_DIR}/src" )

if(USE_NSS) 
	set(check_NSS_SOURCES 
		CSDP_unittest.cpp CSDP_unittest.h 
		GroebnerToSDP_unittest.cpp GroebnerToSDP_unittest.h
		ConstraintMatrixFactory_unittest.cpp ConstraintMatrixFactory_unittest.h
		DenseMatrix_unittest.cpp DenseMatrix_unittest.h

	)
endif()

add_executable(check_${PROJECT_NAME} test.cpp ${check_NSS_SOURCES})

# executable target
add_custom_target( check
                   COMMAND check_${PROJECT_NAME}
                   DEPENDS check_${PROJECT_NAME}
                   COMMENT "${${PROJECT_NAME}_NAME} ${${PROJECT_NAME}_VERSION} CPPUnit Test Suite" )

# link the libraries
target_link_libraries( check_${PROJECT_NAME}
                       ${CPPUNIT_LIBRARIES}
                       ${PROJECT_NAME}
		       ${libraries} )


