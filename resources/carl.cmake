
message(STATUS "Making sure CArL is available.")

set(CARL_BUILD_DIR "${CMAKE_BINARY_DIR}/resources/src/CArL-config-EP-build")
file(MAKE_DIRECTORY ${CARL_BUILD_DIR})
execute_process(
	COMMAND ${CMAKE_COMMAND} -DTARGETDIR=${CMAKE_BINARY_DIR}/resources ${CMAKE_SOURCE_DIR}/resources/carl -DUSE_GINAC=${USE_GINAC}
	WORKING_DIRECTORY ${CARL_BUILD_DIR}
)
execute_process(
	COMMAND ${CMAKE_COMMAND} --build . --target CArL-EP-download
	WORKING_DIRECTORY ${CARL_BUILD_DIR}
)

ExternalProject_Add(
	CArL-EP
	DOWNLOAD_COMMAND ""
	CONFIGURE_COMMAND ""
	BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} resources carl carl-covering carl-cad carl-io carl-model carl-settings
	INSTALL_COMMAND ${CMAKE_MAKE_PROGRAM} install/fast
)

ExternalProject_Get_Property(CArL-EP BINARY_DIR)

ExternalProject_Add(
	CArL-EP-doxygen
	BINARY_DIR ${BINARY_DIR}
	DOWNLOAD_COMMAND ""
	CONFIGURE_COMMAND ""
	BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} doxygen-build
	INSTALL_COMMAND ""
)

include(${CMAKE_BINARY_DIR}/resources/src/CArL-EP-build/carlConfig.cmake)
add_dependencies(carl-shared CArL-EP)
add_dependencies(carl-static CArL-EP)
add_dependencies(resources carl-shared carl-static)
