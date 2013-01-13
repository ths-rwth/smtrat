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
	set(mod_version "0.0.0")
	set(mod_settingsClassname " ")
ENDMACRO()

#
MACRO(ModuleMainHeader header)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleMainHeader call, outside of ModuleDefinition")
	endif()
	set(mod_header ${header})
ENDMACRO()

MACRO(ModuleName name)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleName call, outside of ModuleDefinition")
	endif()
	set(mod_name ${name})
ENDMACRO()

MACRO(ModuleClass classname)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleObject call, outside of ModuleDefinition")
	endif()
	set(mod_classname ${classname})
ENDMACRO()

# Set the version
MACRO(ModuleVersion major minor buildnr)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleObject call, outside of ModuleDefinition")
	endif()
	set(mod_version "${major}.${minor}.${buildnr}")
ENDMACRO()


MACRO(ModuleSettingsClass classname)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleSettingsObject call, outside of ModuleDefinition")
	endif()
	set(mod_settingsClassname ${classname})
ENDMACRO()

# Set an additional settingsobject
#
MACRO(ModuleSettingsName settingsname)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleSettingsName call, outside of ModuleDefinition")
	endif()
	set(mod_settingsNames ${mod_settingsNames} ${settingsname})
ENDMACRO()

MACRO(EndDefineModule)
	# Number of modules (for determining this modules number) 
	list(LENGTH moduleTypes mod_index)
	

	if(defineModule)
		set(moduleMainHeaders ${moduleMainHeaders} ${mod_header} PARENT_SCOPE)
		set(moduleTypes ${moduleTypes} ${mod_name} PARENT_SCOPE)
		set(moduleClasses ${moduleClasses} ${mod_classname} PARENT_SCOPE)
		set(moduleVersions ${moduleVersions} ${mod_version} PARENT_SCOPE)
		set(moduleSettingsClasses ${moduleSettingsClasses} ${mod_settingsClassname} PARENT_SCOPE)
		set(moduleSettingsList_${mod_index} ${mod_settingsNames} PARENT_SCOPE)
		message("${moduleSettingsList_0}")
		set(defineModule 0)
	else()
		message(FATAL_ERROR "Invalid EndDefineModule call, outside of ModuleDefinition")
	endif()
ENDMACRO()

