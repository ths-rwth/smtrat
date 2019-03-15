add_executable( delta
	delta.cpp
)

target_link_libraries( delta Boost_program_options_SHARED )

if (NOT WIN32)
	target_link_libraries( delta pthread )
endif()

set_target_properties( delta PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )
