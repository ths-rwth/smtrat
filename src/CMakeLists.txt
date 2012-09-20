add_subdirectory(lib)
add_subdirectory(solver)

# unit tests
# # # # # # #

if(CppUnit_FOUND)
    add_subdirectory(test)
endif()


add_subdirectory(gui EXCLUDE_FROM_ALL)