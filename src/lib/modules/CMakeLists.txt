# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/lib/modules/CMakeLists.txt                        #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project page: https://github.com/smtrat/smtrat/wiki         #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-04-18                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ListSubDirs(SUBDIRS ${CMAKE_SOURCE_DIR}/src/lib/modules)
foreach(subdir ${SUBDIRS})
    add_subdirectory(${subdir})
endforeach()

# Number of modules (for iteration)
list(LENGTH moduleTypes nrModules)
math(EXPR maxModIndex "${nrModules} - 1")

# write Modules.h
foreach(header ${moduleMainHeaders})
	set(includeHeaders "${includeHeaders}#include \"${header}\"\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h )

# write Modules.cpp
foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleVersions ${modIndex} modVersion)
  list(GET moduleSettingsClasses ${modIndex} modSettingsClass)
  set(moduleInfoString "${moduleInfoString} \\
---------------------------------- \\n \\
Module name: ${modType} \\n \\
Module version: ${modVersion} \\n \\
Module settings classname: ${modSettingsClass} \\n \\
Module settings: ${moduleSettingsList_${modIndex}} \\n")

	string(REPLACE "Module" "" Prefix ${modType})
	if (EXISTS "${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/${Prefix}Settings.h.in")
		configure_file( "${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/${Prefix}Settings.h.in" "${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/${Prefix}Settings.h" )
	endif()
	if (EXISTS "${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/Instantiation.h.in")
		file(READ "${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/${Prefix}Settings.h" Content)
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
			set(INSTANTIATIONS "${INSTANTIATIONS}template class ${modType}<${setting}>;\n")
		endforeach()
		configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/Instantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/${modType}/Instantiation.h )
	endif()

endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp )


foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleSettingsClasses ${modIndex} modSettClass)

  if( modSettClass STREQUAL " ")
    # modType unchanged
	set(moduleTypesSettings ${moduleTypesSettings} ${modType})
  else()
	list(LENGTH moduleSettingsList_${modIndex} modNrSettings)
	if( modNrSettings GREATER 1 )
		# multiple settings instances
		foreach(modSettingsName ${moduleSettingsList_${modIndex}})
			# modType changed
			set(moduleTypesSettings ${moduleTypesSettings} ${modType}_${modSettingsName})
		endforeach()

	else()
		# exactly one settings instance
		list(GET moduleSettingsList_${modIndex} 0 modSettingsName)

		# modType unchanged
		set(moduleTypesSettings ${moduleTypesSettings} ${modType})
	endif()
  endif()
endforeach()

# propagate and enhance source file definitions
set(lib_modules_src
	${moduleSources}
	modules/Modules.cpp
	PARENT_SCOPE)

# propagate additional library information
set(libraries ${moduleLibraries} ${libraries} PARENT_SCOPE)
