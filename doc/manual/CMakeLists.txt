set(MODULE_INCLUDES "")
ListSubDirs(MODULES ${CMAKE_SOURCE_DIR}/src/smtrat-modules)
foreach(module ${MODULES})
	if(EXISTS ${CMAKE_SOURCE_DIR}/src/smtrat-modules/${module}/${module}.md)
		set(MODULE_INCLUDES "${MODULE_INCLUDES}\n@subpage ${module}\n")
	endif()
endforeach()

configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/modules/modules.md.in ${CMAKE_CURRENT_SOURCE_DIR}/modules/modules.md )
