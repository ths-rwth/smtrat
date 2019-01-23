include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)
add_custom_target(smtrat-modules-all)

file(GLOB modules RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *Module/)
foreach(module ${modules})
	if (IS_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/${module})

		# Properly configure everything but Instantiation.h
		file(GLOB_RECURSE tpl_files "*.in")
		foreach(tpl ${tpl_files})
			if(NOT tpl MATCHES ".*/Instantiation.h.in")
				string(REGEX REPLACE ".in$" "" file ${tpl})
				configure_file("${tpl}" "${file}")
			endif()
		endforeach()
	
		# Properly configure Instantiation.h
		if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${module}/Instantiation.h.in")
			string(REPLACE "Module" "" Prefix ${module})
			file(READ "${CMAKE_CURRENT_SOURCE_DIR}/${module}/${Prefix}Settings.h" Content)
			string(REGEX MATCHALL "[^_0-9a-zA-Z]${Prefix}Settings[_0-9a-zA-Z]+" Matches ${Content})
			
			set(settings "")
			foreach(Match ${Matches})
				string(SUBSTRING ${Match} 1 -1 Match)
				list(APPEND settings ${Match})
			endforeach()
			list(SORT settings)
			list(REMOVE_DUPLICATES settings)
			set(INSTANTIATIONS "")
			foreach(setting ${settings})
				set(INSTANTIATIONS "${INSTANTIATIONS}template class ${module}<${setting}>;\n")
			endforeach()
			configure_file("${CMAKE_CURRENT_SOURCE_DIR}/${module}/Instantiation.h.in" "${CMAKE_CURRENT_SOURCE_DIR}/${module}/Instantiation.h")
		endif()

		# Create library
		file(GLOB_RECURSE sources ${CMAKE_CURRENT_SOURCE_DIR}/${module}/*.cpp)
		
		add_new_libraries(smtrat-module-${module} ${PROJECT_VERSION_LIB} "${sources}" "resources")
		target_include_dirs_from(smtrat-module-${module}-objects "" PUBLIC carl-shared smtrat-common-shared)
		target_link_libraries(smtrat-module-${module}-shared smtrat-common-shared smtrat-modules-shared)
		target_link_libraries(smtrat-module-${module}-static smtrat-common-static smtrat-modules-static)
		install_libraries(smtrat-module-${module}-shared smtrat-module-${module}-static)

		add_dependencies(smtrat-modules-all smtrat-module-${module}-shared smtrat-module-${module}-static)

		unset(DEPEND-include)
		unset(DEPEND-shared)
		unset(DEPEND-static)
		add_subdirectory(${module})
		if(DEPEND-include OR DEPEND-shared OR DEPEND-static)
			target_include_dirs_from(smtrat-module-${module}-objects "" PUBLIC ${DEPEND-include})
			target_link_libraries(smtrat-module-${module}-shared ${DEPEND-shared})
			target_link_libraries(smtrat-module-${module}-static ${DEPEND-static})
		endif()

		if (CLANG_TIDY)
			add_custom_target(tidy-module-${module}
				COMMAND clang-tidy -p ${CMAKE_BINARY_DIR}/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='.*' ${sources}
				WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			)
		endif()
	endif()
endforeach()

file(GLOB smtrat-modules_sources "*.cpp")

add_new_libraries(smtrat-modules "${PROJECT_VERSION_LIB}" "${smtrat-modules_sources}" "resources")
target_include_dirs_from(smtrat-modules-objects "" PUBLIC smtrat-common-shared)
target_link_libraries(smtrat-modules-shared smtrat-common-shared)
target_link_libraries(smtrat-modules-static smtrat-common-static)

install_libraries(smtrat-modules-shared smtrat-modules-static)
