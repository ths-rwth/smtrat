function(set_version major minor)
	execute_process(
		COMMAND git describe --match "[0-9]*.[0-9]*"
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
		OUTPUT_VARIABLE GIT_VERSION
		OUTPUT_STRIP_TRAILING_WHITESPACE
	)
	set(patch "")
	if (GIT_VERSION MATCHES "([0-9]+)\.([0-9]+)(-?.*)")
		set(major ${CMAKE_MATCH_1})
		set(minor ${CMAKE_MATCH_2})
		if (CMAKE_MATCH_3 MATCHES "-([0-9]+)-(g[0-9a-f]+)")
			set(patch_full "${CMAKE_MATCH_1}-${CMAKE_MATCH_2}")
			set(patch "${CMAKE_MATCH_1}")
		endif()
	else()
		message(STATUS "Could not parse version from git, using default ${major}.${minor}")
	endif()
	
	set(PROJECT_VERSION_MAJOR ${major} PARENT_SCOPE)
	set(PROJECT_VERSION_MINOR ${minor} PARENT_SCOPE)
	set(PROJECT_VERSION_PATCH ${patch} PARENT_SCOPE)
	if(patch)
		set(PROJECT_VERSION_FULL "${major}.${minor}.${patch_full}" PARENT_SCOPE)
		set(PROJECT_VERSION "${major}.${minor}.${patch}" PARENT_SCOPE)
	else()
		set(PROJECT_VERSION_FULL "${major}.${minor}" PARENT_SCOPE)
		set(PROJECT_VERSION "${major}.${minor}" PARENT_SCOPE)
	endif()
endfunction(set_version)

macro(install_libraries target)
	install(
		TARGETS "${target}"
		EXPORT smtratTargets
		RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
		LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
		ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
	)
endmacro(install_libraries)