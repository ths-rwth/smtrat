# - Try to find GiNaC
# Originally from Martin Velis
#

SET (GINACRA_FOUND FALSE)

FIND_PATH (GINACRA_INCLUDE_DIR ginacra.h
        /usr/include/ginacra 
        /usr/local/include/ginacra 
        /opt/local/include/ginacra
        $ENV{UNITTESTXX_PATH}/src 
        $ENV{UNITTESTXX_INCLUDE_PATH}
        )

FIND_LIBRARY (GINACRA_LIBRARY NAMES ginacra PATHS 
        /usr/lib 
        /usr/local/lib 
        /opt/local/lib 
        $ENV{UNITTESTXX_PATH} 
        ENV{UNITTESTXX_LIBRARY_PATH}
        )

IF (GINACRA_INCLUDE_DIR AND GINACRA_LIBRARY)
        SET (GINACRA_FOUND TRUE)
ENDIF (GINACRA_INCLUDE_DIR AND GINACRA_LIBRARY)

IF (GINACRA_FOUND)
   IF (NOT GiNaC_FIND_QUIETLY)
      MESSAGE(STATUS "Found GiNaCRA: ${GINACRA_LIBRARY}")
   ENDIF (NOT GiNaC_FIND_QUIETLY)
ELSE (GINACRA_FOUND)
   IF (GiNaC_FIND_REQUIRED)
      MESSAGE(FATAL_ERROR "Could not find GiNaC")
   ENDIF (GiNaC_FIND_REQUIRED)
ENDIF (GINACRA_FOUND)

MARK_AS_ADVANCED (	GINACRA_FOUND
					GINACRA_INCLUDE_DIR
					GINACRA_LIBRARY
				 )