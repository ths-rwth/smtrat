find_package(GMP ${GMPXX_FIND_VERSION} QUIET)

if(GMP_FOUND)
	# Include dir
	find_path(GMPXX_INCLUDE_DIR
		NAMES gmpxx.h 
		HINTS ${GMP_INCLUDE_DIR}
		DOC "Include directory for GMPXX"
	)
	
	# Library files
	get_filename_component(GMP_LIB_PATH ${GMP_LIBRARY} DIRECTORY)
	find_library(GMPXX_LIBRARY
		NAMES gmpxx
		HINTS ${GMP_LIB_PATH}
	)
	
	if(GMPXX_INCLUDE_DIR AND GMPXX_LIBRARY)
		set(GMPXX_FOUND TRUE)
	endif()
	
	mark_as_advanced(
		GMPXX_FOUND
		GMPXX_INCLUDE_DIR
		GMPXX_LIBRARY
	)
else()
	message(STATUS "Did not search for GMPXX, GMP is missing.")
endif()
