option( USE_BOOST_REGEX "Use boost::regex instead of std::regex in delta." OFF )

configure_file( ${CMAKE_SOURCE_DIR}/src/delta/config.h.in ${CMAKE_SOURCE_DIR}/src/delta/config.h )

add_executable( delta
	delta.cpp
)

target_link_libraries( delta boost_program_options )

if (NOT WIN32)
	target_link_libraries( delta pthread )
endif()

if(USE_BOOST_REGEX)
	target_link_libraries( delta boost_regex )
endif()

set_target_properties( delta PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR} )

