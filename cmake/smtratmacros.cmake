# File: macros.cmake
# Authors: Sebastian Junges, Ulrich Loup
# Erstellt: 2013-04-11
# Version: 2013-04-18
#
# This file contains several macros which are used in this project. Notice that several are copied straight from web ressources.

# Macro
# List handling macros
# Source: http://www.cmake.org/pipermail/cmake/2004-June/005187.html 12.6.2015

MACRO(LIST_APPEND var value)
     SET(${var} ${${var}} ${value})
ENDMACRO(LIST_APPEND)

MACRO(LIST_APPEND_UNIQUE var value)
     SET(LIST_ADD_UNIQUE_FLAG 0)
     FOREACH(i ${${var}})
         IF ("${i}" STREQUAL "${value}")
             SET(LIST_ADD_UNIQUE_FLAG 1)
         ENDIF("${i}" STREQUAL "${value}")
     ENDFOREACH(i)
     IF(NOT LIST_ADD_UNIQUE_FLAG)
         SET(${var} ${${var}} ${value})
     ENDIF(NOT LIST_ADD_UNIQUE_FLAG)
ENDMACRO(LIST_APPEND_UNIQUE)

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

MACRO(AddModuleLibrary lib)
    if(NOT defineModule)
		message(FATAL_ERROR "Invalid AddModuleSource call, outside of ModuleDefinition")
	endif()
	set(moduleLibraries ${lib} ${moduleLibraries})
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

# Function
# collect_files in subdirectories and save them into variables
# Igor Bongartz 06.2015

function(collect_files prefix name)
  file(GLOB_RECURSE subfiles RELATIVE ${CMAKE_CURRENT_SOURCE_DIR}/${name} ${name}/*)

  foreach(subfile ${subfiles})
    if(${subfile} MATCHES ".*([.]in)")
      string(REGEX REPLACE ".in" "" subfile_name ${subfile})
      configure_file(${CMAKE_SOURCE_DIR}/src/${prefix}/${name}/${subfile} ${CMAKE_SOURCE_DIR}/src/${prefix}/${name}/${subfile_name})

    elseif((${subfile} MATCHES ".*([.]h)") OR (${subfile} MATCHES ".*([.]tpp)"))
      get_filename_component(subdir ${subfile} DIRECTORY)
      if(NOT ${subdir} STREQUAL "")
        LIST_APPEND_UNIQUE(${prefix}_${name}_subdir ${subdir})
        list(APPEND ${prefix}_${name}_${subdir}_headers ${name}/${subfile})
      endif()
      list(APPEND ${prefix}_${name}_headers ${name}/${subfile})

    elseif(${subfile} MATCHES ".*([.]cpp)")
      list(APPEND ${prefix}_${name}_src ${name}/${subfile})
    endif()
  endforeach()

  foreach(subdir ${${prefix}_${name}_subdir})
    install(FILES			${${prefix}_${name}_${subdir}_headers}
    DESTINATION		include/${prefix}/${name}/${subdir})
  endforeach()

	#Install
	install(FILES			${${prefix}_${name}_headers}
			DESTINATION		include/${prefix}/${name})

	#SET the scope
	set(${prefix}_${name}_headers ${${prefix}_${name}_headers} PARENT_SCOPE)
	set(${prefix}_${name}_src ${${prefix}_${name}_src} PARENT_SCOPE)
endfunction(collect_files)

MACRO(ADD_PRECOMPILED_HEADER PrecompiledHeader PrecompiledSource SourcesVar)
  GET_FILENAME_COMPONENT(PrecompiledBasename ${PrecompiledHeader} NAME_WE)
  SET(PrecompiledBinary "${CMAKE_CURRENT_BINARY_DIR}/${PrecompiledBasename}.pch")
  SET(Sources ${${SourcesVar}})

  SET_SOURCE_FILES_PROPERTIES(${PrecompiledSource}
                              PROPERTIES COMPILE_FLAGS "/Yc\"${PrecompiledHeader}\" /Fp\"${PrecompiledBinary}\""
                                         OBJECT_OUTPUTS "${PrecompiledBinary}")
  SET_SOURCE_FILES_PROPERTIES(${Sources}
                              PROPERTIES COMPILE_FLAGS "/Yu\"${PrecompiledHeader}\" /FI\"${PrecompiledHeader}\" /Fp\"${PrecompiledBinary}\""
                                         OBJECT_DEPENDS "${PrecompiledBinary}")
  # Add precompiled header to SourcesVar
  LIST(APPEND ${SourcesVar} ${PrecompiledSource})
ENDMACRO(ADD_PRECOMPILED_HEADER)
