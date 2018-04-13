# File: macros.cmake
# Authors: Sebastian Junges, Ulrich Loup
# Erstellt: 2013-04-11
# Version: 2013-04-18
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
MACRO(BeginDefineModule)
	set(defineModule 1)
	set(mod_version "0.0.0")
	set(mod_settingsClassname " ")
	set(mod_default_enable OFF)
ENDMACRO()

MACRO(ModuleMainHeader header)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleMainHeader call, outside of ModuleDefinition")
	endif()
	set(mod_header ${header})
ENDMACRO()

MACRO(AddModuleSource source)
    if(NOT defineModule)
		message(FATAL_ERROR "Invalid AddModuleSource call, outside of ModuleDefinition")
	endif()
	set(moduleSources ${source} ${moduleSources})
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

MACRO(ModuleDefaultEnabled)
	if(NOT defineModule)
		message(FATAL_ERROR "Invalid ModuleDefaultEnable call, outside of ModuleDefinition")
	endif()
	set(mod_default_enable ON)
ENDMACRO()

MACRO(EndDefineModule)
	if( NOT defineModule )
		message(FATAL_ERROR "Invalid EndDefineModule call, outside of ModuleDefinition")
	endif()

	set(allModuleTypes ${allModuleTypes} ${mod_name} PARENT_SCOPE)
	# Number of modules (for determining this modules number)
	list(LENGTH moduleTypes mod_index)

    FILE(GLOB_RECURSE sources *.cpp)
    foreach(src ${sources})
        AddModuleSource(${src})
    endforeach()

	set(moduleMainHeaders ${moduleMainHeaders} ${mod_header} PARENT_SCOPE)
	set(moduleSources ${moduleSources} PARENT_SCOPE)
	set(moduleLibraries ${moduleLibraries} PARENT_SCOPE)
	set(moduleTypes ${moduleTypes} ${mod_name} PARENT_SCOPE)
	set(moduleClasses ${moduleClasses} ${mod_classname} PARENT_SCOPE)
	set(moduleVersions ${moduleVersions} ${mod_version} PARENT_SCOPE)
	set(moduleSettingsClasses ${moduleSettingsClasses} ${mod_settingsClassname} PARENT_SCOPE)
	set(moduleSettingsList_${mod_index} ${mod_settingsNames} PARENT_SCOPE)

	set(defineModule 0)
ENDMACRO()

FUNCTION(add_imported_library name type lib include)
	# Workaround from https://cmake.org/Bug/view.php?id=15052
	file(MAKE_DIRECTORY "${include}")
	if("${lib}" STREQUAL "")
		if("${type}" STREQUAL "SHARED")
			add_library(${name} INTERFACE IMPORTED GLOBAL)
			set_target_properties(${name} PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${include}")
		endif()
	else()
		set(lib_list "${lib}")
		list(LENGTH lib_list NumFiles)
		if(NumFiles GREATER 1)
			add_library(${name}_${type} INTERFACE IMPORTED GLOBAL)
			set(shortnames "${ARGN}")
			set(libs "")
			math(EXPR range "${NumFiles}-1")
			foreach(index RANGE ${range})
				list(GET lib_list ${index} l)
				list(GET shortnames ${index} shortname)
				add_imported_library("${name}_${shortname}" ${type} ${l} ${include})
				list(APPEND libs "${name}_${shortname}_${type}")
				# only from cmake 3.3 https://github.com/ceph/ceph/pull/7128
				#add_dependencies(${name}_${type} ${name}_${shortname}_${type})
			endforeach()
			set_target_properties(${name}_${type} PROPERTIES INTERFACE_LINK_LIBRARIES "${libs}")
			set_target_properties(${name}_${type} PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${include}")
		else()
			add_library(${name}_${type} ${type} IMPORTED GLOBAL)
			set_target_properties(${name}_${type} PROPERTIES IMPORTED_LOCATION "${lib}")
			set_target_properties(${name}_${type} PROPERTIES INTERFACE_INCLUDE_DIRECTORIES "${include}")
			if(WIN32)
				string(REPLACE "dll" "lib" IMPLIB ${lib})
				set_target_properties(${name}_${type} PROPERTIES IMPORTED_IMPLIB "${IMPLIB}")
			endif()
		endif()
	endif()
ENDFUNCTION(add_imported_library)

macro(load_library group name version)
    string(TOUPPER ${name} LIBNAME)
    set(CMAKE_FIND_LIBRARY_SUFFIXES "${DYNAMIC_EXT};${STATIC_EXT}")
    set(Boost_USE_STATIC_LIBS OFF)
    find_package(${name} ${version} ${ARGN} QUIET)
    if(${name}_FOUND OR ${LIBNAME}_FOUND)
        if (${name}_FOUND)
            set(LIBNAME ${name})
        endif()

		if(LIBNAME MATCHES "Boost")
			add_imported_library(${LIBNAME} SHARED "${${LIBNAME}_LIBRARIES}" "${${LIBNAME}_INCLUDE_DIR}" "${BOOST_COMPONENTS}")
		else()
			add_imported_library(${LIBNAME} SHARED "${${LIBNAME}_LIBRARY}" "${${LIBNAME}_INCLUDE_DIR}")
		endif()

        unset(${LIBNAME}_FOUND CACHE)
        unset(${LIBNAME}_INCLUDE_DIR CACHE)
        unset(${LIBNAME}_LIBRARY CACHE)

        set(CMAKE_FIND_LIBRARY_SUFFIXES "${STATIC_EXT};${DYNAMIC_EXT}")
        set(Boost_USE_STATIC_LIBS ON)
        if (ARGN)
            list(REMOVE_ITEM ARGN "REQUIRED")
        endif()
        find_package(${name} ${version} ${ARGN} QUIET)
        if(${LIBNAME}_FOUND)
			if(LIBNAME MATCHES "Boost")
				add_imported_library(${LIBNAME} STATIC "${${LIBNAME}_LIBRARIES}" "${${LIBNAME}_INCLUDE_DIR}" "${BOOST_COMPONENTS}")
			else()
				add_imported_library(${LIBNAME} STATIC "${${LIBNAME}_LIBRARY}" "${${LIBNAME}_INCLUDE_DIR}")
			endif()
        endif()

        unset(${LIBNAME}_LIBRARY CACHE)
    else()
        message("-- Library ${name} was not found.")
    endif()
endmacro(load_library)


macro(get_include_dir var name)
	get_target_property(INCLUDE_DIR ${name} INTERFACE_INCLUDE_DIRECTORIES)
	set(${var} ${${var}}:${INCLUDE_DIR})
endmacro(get_include_dir)
