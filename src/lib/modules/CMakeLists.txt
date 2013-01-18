ListSubDirs(SUBDIRS ${CMAKE_CURRENT_LIST_DIR})
foreach(subdir ${SUBDIRS})
    add_subdirectory(${subdir})
endforeach()

# Number of modules (for iteration) 
list(LENGTH moduleTypes nrModules)
math(EXPR maxModIndex "${nrModules} - 1")

# write Modules.h
foreach(header ${moduleMainHeaders})
	set(includeHeaders "${includeHeaders} #include \"${header}\" \n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h )

# write Modules.cpp
foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleClasses ${modIndex} modClass)
  list(GET moduleVersions ${modIndex} modVersion)
  list(GET moduleSettingsClasses ${modIndex} modSettingsClass)
  set(moduleInfoString "${moduleInfoString} \\
---------------------------------- \\n \\
Module name: ${modType} \\n \\
Module classname: ${modClass} \\n \\
Module version: ${modVersion} \\n \\
Module settings classname: ${modSettingsClass} \\n \\
Module settings: ${moduleSettingsList_${modIndex}} \\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp )


# write AddModules.h
foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleClasses ${modIndex} modClass)
  list(GET moduleSettingsClasses ${modIndex} modSettClass)

  if( modSettClass STREQUAL " ")
	# no settings instances
	set(addModuleList "${addModuleList}
		manager->addModuleType( MT_${modType}, new StandardModuleFactory< ${modClass} >( ) ); \n")
    # modType unchanged
	set(moduleTypesSettings ${moduleTypesSettings} ${modType})
  else()
	list(LENGTH moduleSettingsList_${modIndex} modNrSettings)
	if( modNrSettings GREATER 1 )
		# multiple settings instances
		foreach(modSettingsName ${moduleSettingsList_${modIndex}})
			set(addModuleList "${addModuleList}
			settingsObjects.push_back(NameAndSettings(\"${modType}_${modSettingsName}\" ,new ${modSettClass}(\"${modSettingsName}\") ) ); 
			manager->addModuleType( MT_${modType}_${modSettingsName}, new StandardModuleFactory< ${modClass} >(settingsObjects.back().second) ); \n")
			# modType changed
			set(moduleTypesSettings ${moduleTypesSettings} ${modType}_${modSettingsName})
		endforeach()

	else()
		# exactly one settings instance
		list(GET moduleSettingsList_${modIndex} 0 modSettingsName)

		set(addModuleList "${addModuleList}
		settingsObjects.push_back(NameAndSettings(\"${modType}\" ,new ${modSettClass}(\"${modSettingsName}\") ) ); 
		manager->addModuleType( MT_${modType}, new StandardModuleFactory< ${modClass} >(settingsObjects.back().second) ); \n")
		# modType unchanged
		set(moduleTypesSettings ${moduleTypesSettings} ${modType})
	endif()
  endif()
endforeach()
configure_file ( ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h )

# write ModuleType.h
foreach(moduleType ${moduleTypesSettings})
	set(moduleTypeList "${moduleTypeList} MT_${moduleType},\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.h )
#write MODULETYPES.TXT
foreach(moduleType ${moduleTypesSettings})
	set(moduleTypeListTXT "${moduleTypeListTXT}\nMT_${moduleType}")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/MODULETYPES.txt.in ${CMAKE_SOURCE_DIR}/src/lib/modules/MODULETYPES.txt )

# write ModuleType.cpp
foreach(moduleType ${moduleTypesSettings})
	set(moduleTypeToStringCases "${moduleTypeToStringCases} \tcase MT_${moduleType}: \n\t{\n\t\t return \"${moduleType}\";\n\t}\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.cpp )


set(lib_modules_src 
	${modulesSources}  
	modules/ModuleType.cpp
	modules/Modules.cpp
	PARENT_SCOPE)

