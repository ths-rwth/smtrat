SET (ReallyNull_FOUND FALSE)
FIND_PATH (ReallyNull_INCLUDE_DIR lib/version.h
        /usr/include/reallynull 
        /usr/local/include/reallynull 
        /opt/local/include/reallynull
        $ENV{UNITTESTXX_PATH}/src 
        $ENV{UNITTESTXX_INCLUDE_PATH}
        )

FIND_LIBRARY (ReallyNull_LIBRARY NAMES reallynull PATHS 
        /usr/lib 
        /usr/local/lib 
        /opt/local/lib 
        $ENV{UNITTESTXX_PATH} 
        ENV{UNITTESTXX_LIBRARY_PATH}
        )

IF (ReallyNull_INCLUDE_DIR AND ReallyNull_LIBRARY)
        SET (ReallyNull_FOUND TRUE)
ENDIF (ReallyNull_INCLUDE_DIR AND ReallyNull_LIBRARY)

IF (ReallyNull_FOUND)
      MESSAGE(STATUS "Found ReallyNull: ${ReallyNull_LIBRARY}")
  ELSE (ReallyNull_FOUND)
   IF (ReallyNull_FIND_REQUIRED)
      MESSAGE(FATAL_ERROR "Could not find GiNaC")
   ENDIF (ReallyNull_FIND_REQUIRED)
ENDIF (ReallyNull_FOUND)

MARK_AS_ADVANCED (	ReallyNull_FOUND
					ReallyNull_INCLUDE_DIR
					ReallyNull_LIBRARY
				 )