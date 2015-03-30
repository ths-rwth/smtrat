add_executable( traceprinter
	main.cpp
)

target_link_libraries( traceprinter )


set_target_properties( traceprinter PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

