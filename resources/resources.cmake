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

##### GMP / GMPXX
if(NOT FORCE_SHIPPED_RESOURCES)
	load_library(smtrat GMP 5.1)
	load_library(smtrat GMPXX 5.1)
endif()
if(GMP_FOUND)
	message(STATUS "Use system version of GMP/GMPXX ${GMP_VERSION}")
else()
	set(GMP_VERSION "6.1.0")
	include(resources/gmp.cmake)
	message(STATUS "Use shipped version of GMP/GMPXX ${GMP_VERSION}")
endif()

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

##### CoCoALib
if(USE_COCOA)
	if(NOT FORCE_SHIPPED_RESOURCES)
		load_library(smtrat CoCoA 0.99542)
	endif()
	if(COCOA_FOUND)
		message(STATUS "Use system version of CoCoA ${COCOA_VERSION}")
	else()
		# Depends on GMP
		set(COCOA_VERSION "0.99551")
		set(COCOA_TGZHASH "0e75ba96e627f955adbb17c037d5bcdf")
		include(resources/cocoa.cmake)
		unset(COCOA_TGZHASH)
		message(STATUS "Use shipped version of CoCoA ${COCOA_VERSION}")
	endif()
else()
	message(STATUS "Usage of CoCoA is disabled")
endif()

##### CArL
find_package(carl)
if(carl_FOUND)
	message(STATUS "Use system version of carl ${carl_VERSION}")
else()
	include(resources/carl.cmake)
	message(STATUS "Use shipped version of carl ${carl_VERSION}")
endif()
