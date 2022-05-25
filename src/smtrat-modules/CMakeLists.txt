include(${carl_INCLUDE_DIR}/../cmake/carlmacros.cmake)

add_definitions(-fPIC)
add_custom_target(smtrat-modules)

file(GLOB modules RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *Module/)
foreach(module ${modules})
	if (IS_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/${module})

		# Properly configure everything but Instantiation.cpp
		file(GLOB_RECURSE tpl_files "*.in")
		foreach(tpl ${tpl_files})
			if(NOT tpl MATCHES ".*/Instantiation.cpp.in")
				string(REGEX REPLACE ".in$" "" file ${tpl})
				configure_file("${tpl}" "${file}")
			endif()
		endforeach()

		# Load CMake from module
		unset(DEPEND-include)
		unset(DEPEND-shared)
		unset(DEPEND-static)
		add_subdirectory(${module})

		# Create common library
		file(GLOB_RECURSE sources ${CMAKE_CURRENT_SOURCE_DIR}/${module}/*.cpp)
		list(FILTER sources EXCLUDE REGEX "Instantiation.cpp")
		if (sources)
			add_library(smtrat-module-${module}-common-objects OBJECT ${sources})
			add_dependencies(smtrat-module-${module}-common-objects "resources")
			target_include_dirs_from(smtrat-module-${module}-common-objects "" PUBLIC carl-shared smtrat-common-shared)
			if(DEFINED DEPEND-include OR DEFINED DEPEND-shared OR DEFINED DEPEND-static)
				target_include_dirs_from(smtrat-module-${module}-common-objects "" PUBLIC ${DEPEND-include})
			endif()
		endif()
		
		# Create all settings target
		add_custom_target(smtrat-module-${module}-all-static)
		add_custom_target(smtrat-module-${module}-all-shared)

		# Configure module for each setting
		if (EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${module}/Instantiation.cpp.in")
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
			foreach(setting ${settings})
				set(INSTANTIATIONS "template class ${module}<${setting}>;\n")
				configure_file("${CMAKE_CURRENT_SOURCE_DIR}/${module}/Instantiation.cpp.in" "${CMAKE_CURRENT_SOURCE_DIR}/${module}/${setting}Instantiation.cpp")

				# Create library
				file(GLOB_RECURSE sources ${CMAKE_CURRENT_SOURCE_DIR}/${module}/${setting}Instantiation.cpp)
				set(dependencies "resources")
				if(TARGET smtrat-module-${module}-common-objects)
					add_new_libraries_with_objects(smtrat-module-${module}-${setting} ${PROJECT_VERSION_LIB} "${sources}" "${dependencies}" "$<TARGET_OBJECTS:smtrat-module-${module}-common-objects>")
				else()
					add_new_libraries(smtrat-module-${module}-${setting} ${PROJECT_VERSION_LIB} "${sources}" "${dependencies}")
				endif()

				target_include_dirs_from(smtrat-module-${module}-${setting}-objects "" PUBLIC carl-shared smtrat-common-shared)
				target_link_libraries(smtrat-module-${module}-${setting}-shared smtrat-common-shared smtrat-solver-shared)
				target_link_libraries(smtrat-module-${module}-${setting}-static smtrat-common-static smtrat-solver-static)
				if(DEFINED DEPEND-include)
					add_dependencies(smtrat-module-${module}-${setting}-objects ${DEPEND-include})
				endif()
				if(DEFINED DEPEND-include OR DEFINED DEPEND-shared OR DEFINED DEPEND-static)
					add_dependencies(smtrat-module-${module}-${setting}-shared ${DEPEND-include} ${DEPEND-shared})
					add_dependencies(smtrat-module-${module}-${setting}-static ${DEPEND-include} ${DEPEND-static})
					target_include_dirs_from(smtrat-module-${module}-${setting}-objects "" PUBLIC ${DEPEND-include})
					target_link_libraries(smtrat-module-${module}-${setting}-shared ${DEPEND-include} ${DEPEND-shared})
					target_link_libraries(smtrat-module-${module}-${setting}-static ${DEPEND-include} ${DEPEND-static})
				endif()
				install_libraries(smtrat smtrat-module-${module}-${setting}-shared smtrat-module-${module}-${setting}-static)
				add_dependencies(smtrat-module-${module}-all-shared smtrat-module-${module}-${setting}-shared)
				add_dependencies(smtrat-module-${module}-all-static smtrat-module-${module}-${setting}-static)
			endforeach()
		endif()

		add_dependencies(smtrat-modules smtrat-module-${module}-all-shared smtrat-module-${module}-all-static)

		file(GLOB_RECURSE sources ${CMAKE_CURRENT_SOURCE_DIR}/${module}/*.cpp)
		if (CLANG_TIDY)
			add_custom_target(tidy-module-${module}
				COMMAND clang-tidy -p ${CMAKE_BINARY_DIR}/compile_commands.json ${CLANG_TIDY_CHECKS} -header-filter='${CMAKE_CURRENT_SOURCE_DIR}/${module}/' ${sources}
				WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
			)
		endif()
	endif()
endforeach()
