# The module defines the following variables:
#   ANT_EXECUTABLE - path to ant command line client
#   ANT_FOUND - true if the command line client was found
# Example usage:
#   find_package(Ant)
#   if(ANT_FOUND)
#     message("ant found: ${ANT_EXECUTABLE}")
#   endif()

#=============================================================================
# Copyright 2010 Kitware, Inc.
#
# Distributed under the OSI-approved BSD License (the "License");
# see accompanying file Copyright.txt for details.
#
# This software is distributed WITHOUT ANY WARRANTY; without even the
# implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
# See the License for more information.
#=============================================================================
# (To distribute this file outside of CMake, substitute the full
#  License text for the above reference.)

# Look for 'ant'
#
set(ant_names ant)

# Prefer .cmd variants on Windows unless running in a Makefile
# in the MSYS shell.
#
if(WIN32)
  if(NOT CMAKE_GENERATOR MATCHES "MSYS")
    set(ant_names ant.cmd ant eg.cmd eg)
  endif()
endif()

find_program(ANT_EXECUTABLE
  NAMES ${ant_names}
  PATH_SUFFIXES Ant/cmd Ant/bin
  DOC "ant command line client"
  )
mark_as_advanced(ANT_EXECUTABLE)

# Handle the QUIETLY and REQUIRED arguments and set ANT_FOUND to TRUE if
# all listed variables are TRUE

