ListSubDirs(SUBDIRS ${CMAKE_CURRENT_LIST_DIR})
foreach(subdir ${SUBDIRS})
    add_subdirectory(${subdir})
endforeach()

message("${moduleMainHeaders}")
# write Modules.h
foreach(header ${moduleMainHeaders})
	set(includeHeaders "${includeHeaders} #include \"${header}\" \n")
endforeach()
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/Modules.h )

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
list(LENGTH moduleTypes nrModules)
math(EXPR maxModIndex "${nrModules} - 1")

foreach(modIndex RANGE ${maxModIndex})
  list(GET moduleTypes ${modIndex} modType)
  list(GET moduleObjects ${modIndex} modObject)
  set(addModuleList "${addModuleList} manager->addModuleType( MT_${modType}, new StandardModuleFactory< ${modObject} >( ) ); \n")
endforeach()
configure_file ( ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/AddModules.h )


set(lib_modules_src 
	${modulesSources}  
	modules/ModuleType.cpp
	PARENT_SCOPE)

