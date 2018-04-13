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


##### Boost
set(BOOST_COMPONENTS "filesystem;system;program_options;regex")
set(Boost_USE_DEBUG_RUNTIME "OFF")
if(NOT FORCE_SHIPPED_RESOURCES)
	load_library(smtrat Boost 1.55 COMPONENTS ${BOOST_COMPONENTS})
endif()
if(Boost_FOUND)
	message(STATUS "Use system version of Boost ${Boost_VERSION}")
else()
	set(BOOST_VERSION "1.64.0")
	set(BOOST_ZIPHASH "36093e4018aecd5b0e31e80457ac5fc1")
	include(resources/boost.cmake)
	message(STATUS "Use shipped version of Boost ${BOOST_VERSION}")
endif()

##### CArL
#find_package(carl)
if(carl_FOUND)
	message(STATUS "Use system version of carl ${carl_VERSION}")
else()
	include(resources/carl.cmake)
	message(STATUS "Use shipped version of carl ${carl_VERSION}")
endif()
