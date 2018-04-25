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
find_package(carl)
if(carl_FOUND)
	message(STATUS "Use system version of carl ${carl_VERSION}")
else()
	include(resources/carl.cmake)
	message(STATUS "Use shipped version of carl ${carl_VERSION}")
endif()
