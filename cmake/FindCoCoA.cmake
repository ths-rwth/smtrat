# Include dir
find_path(COCOA_INCLUDE_DIR
	NAMES CoCoA/library.H
	PATHS
		/usr/include/
		/usr/local/include/
	DOC "Include directory for CoCoA"
)

find_library(COCOA_LIBRARY
	NAMES cocoa
	PATHS
		/usr/lib 
		/usr/local/lib 
)

if(COCOA_INCLUDE_DIR AND COCOA_LIBRARY)
	set(COCOA_FOUND TRUE)

	# Version
	function(GetVersion OUTPUT FILENAME)
		file(STRINGS ${FILENAME} RES REGEX "CoCoALib version .*")
		string(REGEX MATCH "[0-9]+\.[0-9]+" RES "${RES}")
		set(${OUTPUT} "${RES}" PARENT_SCOPE)
	endfunction()
	GetVersion(COCOA_VERSION "${COCOA_INCLUDE_DIR}/CoCoA/library.H")

	if(COCOA_FIND_VERSION VERSION_GREATER COCOA_VERSION)
		message(WARNING "Required CoCoA ${COCOA_FIND_VERSION} but found only CoCoA ${COCOA_VERSION}.")
		return()
	endif()
endif()

mark_as_advanced(
	COCOA_FOUND
	COCOA_INCLUDE_DIR
	COCOA_LIBRARY
	COCOA_VERSION
)
