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

MACRO(CMAKE_INCLUDE_MODULEOPTIONS )

ENDMACRO()

#install all headers recursively 
MACRO(INSTALL_HEADERS_RECURSIVELY )

ENDMACRO()

#
MACRO(ModuleMainHeader header)
set(moduleMainHeaders ${moduleMainHeaders} ${header} PARENT_SCOPE)
ENDMACRO()

MACRO(ModuleName name)
set(moduleTypes ${moduleTypes} ${name} PARENT_SCOPE)
ENDMACRO()

MACRO(ModuleObject objectname)
set(moduleObjects ${moduleObjects} ${objectname} PARENT_SCOPE)
ENDMACRO()

