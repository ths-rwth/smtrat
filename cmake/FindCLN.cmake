# - Try to find CLN
# Once done, this will define
#
#  CLN_FOUND          - system has CLN
#  CLN_INCLUDE_DIR    - the CLN include directory
#  CLN_LIBRARY        - the CLN library location

include(LibFindMacros)

# Dependencies
libfind_package(cln REQUIRED)

# Use pkg-config to get hints about paths
libfind_pkg_check_modules(CLN_PKGCONF cln)

# Include dir
find_path(CLN_INCLUDE_DIR
  NAMES cln/cln.h
  HINTS ${CLN_PKGCONF_INCLUDE_DIRS}
)

# Finally the library itself
find_library(CLN_LIBRARY
  NAMES cln
  HINTS ${CLN_PKGCONF_LIBRARY_DIRS}
)

# Set the include dir variables and the libraries and let libfind_process do the rest.
# NOTE: Singular variables for this library, plural for libraries this this lib depends on.
set(CLN_PROCESS_INCLUDES CLN_INCLUDE_DIR CLN_INCLUDE_DIR)
set(CLN_PROCESS_LIBS CLN_LIBRARY CLN_LIBRARY)
libfind_process(CLN)
