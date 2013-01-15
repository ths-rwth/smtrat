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
Module settings: ${moduleSettingsList_${modIndex}}")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.cpp )

# write ModuleType.h
foreach(moduleType ${moduleTypes})
	set(moduleTypeList "${moduleTypeList} MT_${moduleType},\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.h )

# write ModuleType.cpp
foreach(moduleType ${moduleTypes})
	set(moduleTypeToStringCases "${moduleTypeToStringCases} \tcase MT_${moduleType}: \n\t{\n\t\t return \"${moduleType}\";\n\t}\n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ModuleType.cpp )

# write AddModules.h
foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleClasses ${modIndex} modClass)
  list(GET moduleSettingsClasses ${modIndex} modSettClass)

  if( modSettClass STREQUAL " ")
	set(addModuleList "${addModuleList} manager->addModuleType( MT_${modType}, new StandardModuleFactory< ${modClass} >( ) ); \n")
  else()
	set(addModuleList "${addModuleList}
	settingsObjects.push_back(new ${modSettClass}()); 
	manager->addModuleType( MT_${modType}, new StandardModuleFactory< ${modClass} >(settingsObjects.back()) ); \n")
  endif()
endforeach()
configure_file ( ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h )

set(lib_modules_src 
	${modulesSources}  
	modules/ModuleType.cpp
	modules/Modules.cpp
	PARENT_SCOPE)

