set(CARL_BUILD_DIR "${CMAKE_BINARY_DIR}/resources/src/CArL-config-EP-build")
file(MAKE_DIRECTORY ${CARL_BUILD_DIR})
execute_process(
	COMMAND ${CMAKE_COMMAND} -DTARGETDIR=${CMAKE_BINARY_DIR}/resources ${CMAKE_SOURCE_DIR}/resources/carl
	WORKING_DIRECTORY ${CARL_BUILD_DIR}
	OUTPUT_QUIET
)
message(STATUS "Cloning carl to ${CARL_BUILD_DIR}")
execute_process(
	COMMAND ${CMAKE_COMMAND} --build . --target CArL-EP
	WORKING_DIRECTORY ${CARL_BUILD_DIR}
	OUTPUT_QUIET
)

ExternalProject_Add(
	CArL-EP
	DOWNLOAD_COMMAND ""
	CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> -DCMAKE_PREFIX_PATH=<INSTALL_DIR> -DBUILD_DOXYGEN=ON -DBUILD_STATIC=ON -DUSE_BLISS=ON -DUSE_COCOA=ON -DEXPORT_TO_CMAKE=OFF
	BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} lib_carl lib_carl_static
	INSTALL_COMMAND ${CMAKE_MAKE_PROGRAM} install/fast
)

include(${CMAKE_BINARY_DIR}/resources/src/CArL-EP-build/carlConfig.cmake)
add_dependencies(lib_carl CArL-EP)
add_dependencies(lib_carl_static CArL-EP)
add_dependencies(resources lib_carl lib_carl_static)
