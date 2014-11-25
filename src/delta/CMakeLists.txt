add_executable( delta
	delta.cpp
)

target_link_libraries( delta boost_program_options boost_regex )

set_target_properties( delta PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

