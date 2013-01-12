# File: macros.cmake
# Author: Sebastian Junges
# Version: 11-01-2013
#
# This file contains several macros which are used in this project. Notice that several are copied straight from web ressources.

# Macro
# List Subdirectories
# Source: http://stackoverflow.com/questions/7787823/cmake-how-to-get-the-name-of-all-subdirectories-of-a-directory
MACRO(ListSubDirs result curdir)
  FILE(GLOB children RELATIVE ${curdir} ${curdir}/*)
  SET(dirlist "")
  FOREACH(child ${children})
    IF(IS_DIRECTORY ${curdir}/${child})
        SET(dirlist ${dirlist} ${child})
    ENDIF()
  ENDFOREACH()
  SET(${result} ${dirlist})
ENDMACRO()

# Macro 
# Find and include all cmake pathes recursively
# Based on: http://www.vtk.org/Wiki/CMake/Examples#Recursively_add_subdirectories_to_INCLUDE_DIRECTORIES
MACRO(CMAKE_DIRECTORIES return_list)
    FILE(GLOB_RECURSE new_list *.cmake)
    SET(dir_list "")
    FOREACH(file_path ${new_list})
        GET_FILENAME_COMPONENT(dir_path ${file_path} PATH)
        SET(dir_list ${dir_list} ${dir_path})
    ENDFOREACH()
    LIST(REMOVE_DUPLICATES dir_list)
    SET(${return_list} ${dir_list})
ENDMACRO()

MACRO(BeginDefineModule)
	set(defineModule 1)
ENDMACRO()

#
MACRO(ModuleMainHeader header)
	if(defineModule)
		set(mod_header ${header})
	else()
		message(FATAL_ERROR "Invalid ModuleMainHeader call, outside of ModuleDefinition")
	endif()
ENDMACRO()

MACRO(ModuleName name)
	if(defineModule)
		set(mod_name ${name})
	else()
		message(FATAL_ERROR "Invalid ModuleName call, outside of ModuleDefinition")
	endif()
ENDMACRO()

MACRO(ModuleObject objectname)
	if(defineModule)
		set(mod_objectname ${objectname})
	else()
		message(FATAL_ERROR "Invalid ModuleObject call, outside of ModuleDefinition", ERROR)
	endif()
ENDMACRO()

MACRO(ModuleVersion major minor buildnr)
	if(defineModule)
		set(mod_version "${major}.${minor}.${buildnr}")
	else()
		message(FATAL_ERROR "Invalid ModuleObject call, outside of ModuleDefinition", ERROR)
	endif()
ENDMACRO()

MACRO(EndDefineModule)
	if(defineModule)
		set(moduleMainHeaders ${moduleMainHeaders} ${mod_header} PARENT_SCOPE)
		set(moduleTypes ${moduleTypes} ${mod_name} PARENT_SCOPE)
		set(moduleObjects ${moduleObjects} ${mod_objectname} PARENT_SCOPE)
		set(moduleVersions ${moduleVersions} ${mod_version} PARENT_SCOPE)
		set(defineModule 0)
	else()
		message(FATAL_ERROR "Invalid EndDefineModule call, outside of ModuleDefinition")
	endif()
ENDMACRO()

