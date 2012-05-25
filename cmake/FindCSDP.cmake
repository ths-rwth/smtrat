# - Try to find CSDP
# Originally from Martin Velis
#

SET (CSDP_FOUND FALSE)

MESSAGE(STATUS "Looking for ${PROJECT_SOURCE_DIR}/external/csdp/include")
FIND_PATH (CSDP_INCLUDE_DIR declarations.h
        ${PROJECT_SOURCE_DIR}/external/csdp/include
		/usr/include/csdp 
        /usr/local/include/csdp 
        /opt/local/include/csdp
        $ENV{UNITTESTXX_PATH}/src 
        $ENV{UNITTESTXX_INCLUDE_PATH}
        )

FIND_LIBRARY (CSDP_LIBRARY NAMES sdp PATHS 
		${PROJECT_SOURCE_DIR}/external/csdp/lib
        /usr/lib 
        /usr/local/lib 
        /opt/local/lib 
        $ENV{UNITTESTXX_PATH} 
        ENV{UNITTESTXX_LIBRARY_PATH}
        )

IF (CSDP_INCLUDE_DIR AND CSDP_LIBRARY)
        SET (CSDP_FOUND TRUE)
ENDIF (CSDP_INCLUDE_DIR AND CSDP_LIBRARY)

IF (CSDP_FOUND)
      MESSAGE(STATUS "Found CSDP: ${CSDP_LIBRARY}")
  ELSE (CSDP_FOUND)
   IF (CSDP_FIND_REQUIRED)
      MESSAGE(FATAL_ERROR "Could not find GiNaC")
   ENDIF (CSDP_FIND_REQUIRED)
ENDIF (CSDP_FOUND)

MARK_AS_ADVANCED (	CSDP_FOUND
					CSDP_INCLUDE_DIR
					CSDP_LIBRARY
				 )