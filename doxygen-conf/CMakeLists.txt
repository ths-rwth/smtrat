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

# Quick self-configuration if only doc is built
if("${PROJECT_NAME}" STREQUAL "")
	cmake_minimum_required (VERSION 2.8 FATAL_ERROR)
	project(SMT-RAT-doxygen NONE)
	set(CMAKE_CURRENT_BINARY_DIR "build")
	set(CMAKE_SOURCE_DIR "..")
	set(PROJECT_SOURCE_DIR "..")
endif()

# Cmake doxygen settings
# # # # # # # # # # # # #

option(DOCUMENTATION_CREATE_PDF "Create PDF reference manual" OFF )
option(DOCUMENTATION_INCLUDE_SOURCE_REFERENCE "Include source reference in manual" ON)

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
	${PROJECT_SOURCE_DIR}/doc/markdown
)
if( DOCUMENTATION_INCLUDE_SOURCE_REFERENCE )
set( DOXYGEN_SOURCE_DIR ${DOXYGEN_SOURCE_DIR} ${PROJECT_SOURCE_DIR}/src )
else(DOCUMENTATION_INCLUDE_SOURCE_REFERENCE )

endif( DOCUMENTATION_INCLUDE_SOURCE_REFERENCE ) 



set(DOXYGEN_OUTPUT_DIR ${PROJECT_BINARY_DIR}/doc )
STRING(REGEX REPLACE ";" " " DOXYGEN_INPUT_LIST "${DOXYGEN_SOURCE_DIR}" )

# Generate doxygen.conf
# # # # # # # # # # # #

get_target_property(DOXYGEN_BIN Doxygen::doxygen IMPORTED_LOCATION)

configure_file(doxygen.conf.in ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf)

# Target for running doxygen
add_custom_target(doc-doxygen
	Doxygen::doxygen ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf
	DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/doxygen.conf Doxygen::doxygen doxygen-build
)

# Target for building the whole documentation
add_custom_target(doc
	DEPENDS doc-doxygen
)

if(DOXYGEN_PDFLATEX)
	set(TEX_DIR ${DOXYGEN_OUTPUT_DIR}/latex)
	add_custom_target(doc-pdf
		BYPRODUCTS ${TEX_DIR}/refman.pdf
		COMMAND ${PDFLATEX_COMPILER} refman.tex
		COMMAND ${PDFLATEX_COMPILER} refman.tex
		COMMAND mv ${TEX_DIR}/refman.pdf ${DOXYGEN_OUTPUT_DIR}/doc_${PROJECT_NAME}-${PROJECT_VERSION}.pdf
		WORKING_DIRECTORY ${TEX_DIR}
		DEPENDS doc-doxygen
	)
	add_dependencies(doc doc-pdf)
endif(DOXYGEN_PDFLATEX)
