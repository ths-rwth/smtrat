# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: manual/CMakeLists.txt                                 #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-02-21                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# Generate manual TeX source
# # # # # # # # # # # # # # #

configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/manual.tex.in ${CMAKE_CURRENT_SOURCE_DIR}/manual.tex )

# Cmake modules needed
# # # # # # # # # # # #

find_package( LATEX )

if( LATEX_COMPILER OR PDFLATEX_COMPILER )
  set(MANUAL_LATEX YES )
else( LATEX_COMPILER OR PDFLATEX_COMPILER )
  set(MANUAL_LATEX NO )
endif( LATEX_COMPILER OR PDFLATEX_COMPILER )

if( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )
  set(MANUAL_PDFLATEX YES )
else( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )
  set(MANUAL_PDFLATEX NO )
endif( PDFLATEX_COMPILER AND ${PROJECT_NAME}_DOC_CREATE_PDF )

# Add "manual" target depending on whether pdflatex is available or not
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

if( MANUAL_PDFLATEX )
  set( TEX_DIR ${CMAKE_CURRENT_SOURCE_DIR} )
  set( PDF_OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/manual.pdf )
  add_custom_command( OUTPUT ${PDF_OUTPUT}
                      COMMAND ${PDFLATEX_COMPILER}
                      ARGS -output-directory=${CMAKE_CURRENT_BINARY_DIR} manual.tex
                      WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} )
  add_custom_target( manual
                     COMMAND mv -T ${PDF_OUTPUT} ${CMAKE_CURRENT_BINARY_DIR}/manual_${PROJECT_NAME}-${PROJECT_VERSION}.pdf
                     DEPENDS ${PDF_OUTPUT} )
endif( MANUAL_PDFLATEX )

