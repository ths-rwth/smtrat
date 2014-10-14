#include_directories(${CMAKE_SOURCE_DIR}/src
#                    ${CMAKE_SOURCE_DIR}/src/delta
#                    ${CMAKE_BINARY_DIR}/src/delta
#                    ${carl_INCLUDE_DIR}
# )

#TODO: we only link against the library, which is copied to the binary root dir. We should somehow save that in a variable.
#link_directories( ${PROJECT_BINARY_DIR}/src/lib
#                  ${PROJECT_BINARY_DIR} )

# executable solver
# # # # # # # # # #

#add_executable( delta
#	delta.cpp
#)

#target_link_libraries( delta
#                        lib_${PROJECT_NAME} # smtrat library
#                        ${libraries} # libraries defined in top-level CMakeLists.txt
#						boost_program_options
#)

#set_target_properties( delta PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

