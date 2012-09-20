add_subdirectory(lib)
if(BUILD_SOLVER)
	add_subdirectory(solver)
endif()
# unit tests
# # # # # # #

if(CppUnit_FOUND)
    add_subdirectory(test)
endif()


add_subdirectory(gui EXCLUDE_FROM_ALL)