# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: doxygen-conf/CMakeLists.txt                           #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-02-21                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# Cmake doxygen settings
# # # # # # # # # # # # #

option(${PROJECT_NAME}_DOC_CREATE_PDF "Create PDF reference manual" ON )

option(MYPROJECT_DOC_WITH_STATIC "Create documentation for static members" ON )
option(MYPROJECT_DOC_WITH_PRIVATE "Create documentation for private members" ON )
option(MYPROJECT_DOC_WITH_LOCAL "Create documentation for local members" ON )
option(MYPROJECT_DOC_WITH_INTERNAL "Create documentation for internal features" OFF )

mark_as_advanced(
	MYPROJECT_DOC_WITH_PRIVATE
	MYPROJECT_DOC_WITH_STATIC
	MYPROJECT_DOC_WITH_LOCAL
	MYPROJECT_DOC_WITH_INTERNAL
 )

# Cmake modules needed
# # # # # # # # # # # #

find_package( HTMLHelp )
find_package( LATEX )

if( HTML_HELP_COMPILER )
  set(DOXYGEN_HTMLHELP YES )
else( HTML_HELP_COMPILER )
  set(DOXYGEN_HTMLHELP NO )
endif( HTML_HELP_COMPILER )

if( LATEX_COMPILER OR PDFLATEX_COMPILER )
  set(DOXYGEN_LATEX YES )
else( LATEX_COMPILER OR PDFLATEX_COMPILER )
  set(DOXYGEN_LATEX NO )
endif( LATEX_COMPILER OR PDFLATEX_COMPILER )

if( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )
  set(DOXYGEN_PDFLATEX YES )
else( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )
  set(DOXYGEN_PDFLATEX NO )
endif( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )

if( MYPROJECT_DOC_CREATE_PDF )
  set(DOXYGEN_PDF_HYPERLINKS YES )
else( MYPROJECT_DOC_CREATE_PDF )
  set(DOXYGEN_PDF_HYPERLINKS NO )
endif( MYPROJECT_DOC_CREATE_PDF )

if( MYPROJECT_DOC_WITH_PRIVATE )
  set(DOXYGEN_EXTRACT_PRIVATE YES )
else( MYPROJECT_DOC_WITH_PRIVATE )
  set(DOXYGEN_EXTRACT_PRIVATE NO )
endif( MYPROJECT_DOC_WITH_PRIVATE )

if( MYPROJECT_DOC_WITH_STATIC )
  set(DOXYGEN_EXTRACT_STATIC YES )
else( MYPROJECT_DOC_WITH_STATIC )
  set(DOXYGEN_EXTRACT_STATIC NO )
endif( MYPROJECT_DOC_WITH_STATIC )

if( MYPROJECT_DOC_WITH_LOCAL )
  set(DOXYGEN_EXTRACT_LOCAL YES )
else( MYPROJECT_DOC_WITH_LOCAL )
  set(DOXYGEN_EXTRACT_LOCAL NO )
endif( MYPROJECT_DOC_WITH_LOCAL )

if( MYPROJECT_DOC_WITH_INTERNAL )
  set(DOXYGEN_EXTRACT_INTERNAL YES )
else( MYPROJECT_DOC_WITH_INTERNAL )
  set(DOXYGEN_EXTRACT_INTERNAL NO )
endif( MYPROJECT_DOC_WITH_INTERNAL )

if( DOT )
  set(HAVE_DOT YES )
else( DOT )
  set(HAVE_DOT NO )
endif( DOT )

# Doxygen settings
# # # # # # # # # #

set(DOXYGEN_LANGUAGE "English" CACHE STRING "Language used by doxygen" )
mark_as_advanced(DOXYGEN_LANGUAGE )

set(DOXYGEN_SOURCE_DIR
	${lib_${PROJECT_NAME}_SRCS}  )
set(DOXYGEN_OUTPUT_DIR doc )
STRING(REGEX REPLACE ";" " " DOXYGEN_INPUT_LIST "${DOXYGEN_SOURCE_DIR}" )

# Generate doxygen.conf
# # # # # # # # # # # #

configure_file( doxygen.conf.in ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf )
add_custom_target( doxygen-doc
		           ${DOXYGEN} ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf
		           DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf )

# Add "doc" target depending on whether pdflatex is available or not
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

if( DOXYGEN_PDFLATEX )
  set( TEX_DIR ${CMAKE_CURRENT_BINARY_DIR}/../${DOXYGEN_OUTPUT_DIR}/latex )
  set( PDF_OUTPUT ${TEX_DIR}/refman.pdf )
  add_custom_command( OUTPUT ${PDF_OUTPUT}
					  POST_BUILD
                      COMMAND ${PDFLATEX_COMPILER}
                      ARGS refman.tex
                      WORKING_DIRECTORY ${TEX_DIR}
                      DEPENDS doxygen-doc )
  add_custom_target( doc
                     COMMAND mv -T ${PDF_OUTPUT} ${CMAKE_CURRENT_BINARY_DIR}/doc_${PROJECT_NAME}-${PROJECT_VERSION}.pdf
                     DEPENDS ${PDF_OUTPUT} )
else( DOXYGEN_PDFLATEX )
  add_custom_target( doc 
                     DEPENDS doxygen-doc )
endif( DOXYGEN_PDFLATEX )

