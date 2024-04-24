include(ExternalProject)
set_directory_properties(PROPERTIES EP_PREFIX ${CMAKE_BINARY_DIR}/resources)

add_custom_target(resources)

if("${CMAKE_GENERATOR}" MATCHES "MAKE")
	set(CMAKE_MAKE_PROGRAM "$(MAKE)")
endif()

# Make sure that libraries from /usr/lib et al are found before OSX frameworks
set(CMAKE_FIND_FRAMEWORK "LAST")

function(print_resource_info name target version)
	if(TARGET ${target})
		get_target_property(TYPE ${target} TYPE)
		if(TYPE STREQUAL "EXECUTABLE")
			get_target_property(PATH1 ${target} IMPORTED_LOCATION)
		elseif(TYPE STREQUAL "SHARED_LIBRARY")
			get_target_property(PATH1 ${target} INTERFACE_INCLUDE_DIRECTORIES)
			get_target_property(PATH2 ${target} IMPORTED_LOCATION)
		elseif(TYPE STREQUAL "STATIC_LIBRARY")
			get_target_property(PATH1 ${target} INTERFACE_INCLUDE_DIRECTORIES)
			get_target_property(PATH2 ${target} IMPORTED_LOCATION)
		elseif(TYPE STREQUAL "INTERFACE_LIBRARY")
			get_target_property(PATH1 ${target} INTERFACE_INCLUDE_DIRECTORIES)
			get_target_property(PATH2 ${target} INTERFACE_LINK_LIBRARIES)
		endif()
		if(PATH1 AND PATH2)
			message(STATUS "${name} ${version} was found at ${PATH1} and ${PATH2}")
		else()
			message(STATUS "${name} ${version} was found at ${PATH1}")
		endif()
	else()
		message(STATUS "${name} was not found.")
	endif()
endfunction(print_resource_info)

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
	set(CARL_REQUIRED_VERSION "19.06")
endif()

find_package(carl ${CARL_REQUIRED_VERSION})

if(carl_FOUND)
	message(STATUS "Use system version of carl ${carl_VERSION} (required ${CARL_REQUIRED_VERSION}) from ${carl_INCLUDE_DIR}")
else()
	include(resources/carl.cmake)
	message(STATUS "Use shipped version of carl ${carl_VERSION} (required ${CARL_REQUIRED_VERSION})")
endif()

add_custom_target(carl-required-version
	COMMAND ${CMAKE_COMMAND} -D CARL_DIR=${carl_INCLUDE_DIR} -D DEST_FILE=${CARL_VERSION_FILE} -P ${CMAKE_SOURCE_DIR}/resources/carl-write-required-version.cmake
	BYPRODUCTS ${CARL_VERSION_FILE}
	WORKING_DIRECTORY ${carl_INCLUDE_DIR}
	VERBATIM
)

##### Doxygen
find_package(Doxygen 1.9.1 QUIET)
if(DOXYGEN_FOUND AND ${CMAKE_VERSION} VERSION_LESS "3.9.0")
	add_executable(Doxygen::doxygen IMPORTED GLOBAL)
	set_target_properties(Doxygen::doxygen PROPERTIES IMPORTED_LOCATION "${DOXYGEN_EXECUTABLE}")
endif()
print_resource_info("Doxygen" Doxygen::doxygen "${DOXYGEN_VERSION}")

if(USE_MIMALLOC)
	include(resources/mimalloc.cmake)
endif()
