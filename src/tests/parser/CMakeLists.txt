add_executable( parserTest
	ParserTest.cpp
)

set_target_properties( parserTest PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

target_link_libraries( parserTest
                        lib_${PROJECT_NAME} # smtrat library
                        ${libraries} # libraries definied in top-level CMakeLists.txt
)

