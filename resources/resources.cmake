include(ExternalProject)
set_directory_properties(PROPERTIES EP_PREFIX ${CMAKE_BINARY_DIR}/resources)

add_custom_target(resources)

if("${CMAKE_GENERATOR}" MATCHES "MAKE")
	set(CMAKE_MAKE_PROGRAM "$(MAKE)")
endif()

# Make sure that libraries from /usr/lib et al are found before OSX frameworks
set(CMAKE_FIND_FRAMEWORK "LAST")

###############
##### Load resources
###############

##### CArL
set(CARL_VERSION_FILE "${CMAKE_SOURCE_DIR}/resources/carl-required.version")
if(EXISTS ${CARL_VERSION_FILE})
	file(READ ${CARL_VERSION_FILE} CARL_REQUIRED_VERSION)
endif()
if (NOT "${CARL_REQUIRED_VERSION}" MATCHES "^[0-9]+\\.[0-9]+(\\.[0-9]+)?$")
	message(STATUS "Resetting invalid carl version ${CARL_REQUIRED_VERSION}")
	set(CARL_REQUIRED_VERSION "0.1")
endif()

find_package(carl ${CARL_REQUIRED_VERSION})

if(carl_FOUND)
	message(STATUS "Use system version of carl ${carl_VERSION} (required ${CARL_REQUIRED_VERSION}) from ${carl_INCLUDE_DIR}")
	add_custom_target(doxygen-build DEPENDS Doxygen::doxygen)
else()
	include(resources/carl.cmake)
	message(STATUS "Use shipped version of carl ${carl_VERSION} (required ${CARL_REQUIRED_VERSION})")
	add_custom_target(doxygen-build DEPENDS Doxygen::doxygen CArL-EP-doxygen)
endif()

add_custom_target(carl-required-version
	COMMAND ${CMAKE_COMMAND} -D CARL_DIR=${carl_INCLUDE_DIR} -D DEST_FILE=${CARL_VERSION_FILE} -P ${CMAKE_SOURCE_DIR}/resources/carl-write-required-version.cmake
	BYPRODUCTS ${CARL_VERSION_FILE}
	WORKING_DIRECTORY ${carl_INCLUDE_DIR}
	VERBATIM
)

ExternalProject_Add(
    Immer-EP
        GIT_REPOSITORY "https://github.com/arximboldi/immer.git"
        DOWNLOAD_NO_PROGRESS 1
        UPDATE_COMMAND "" # due to https://gitlab.kitware.com/cmake/cmake/issues/17229
        CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
	    BUILD_COMMAND ${CMAKE_MAKE_PROGRAM} immer-shared immer-static
        LOG_INSTALL 1
)

ExternalProject_Get_Property(Immer-EP INSTALL_DIR)

add_imported_library(Immer SHARED "" "${INSTALL_DIR}/include")
add_dependencies(resources Immer)

