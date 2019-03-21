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

set(MODULE_INCLUDES "")
ListSubDirs(MODULES ${CMAKE_SOURCE_DIR}/src/lib/modules)
foreach(module ${MODULES})
	if(EXISTS ${CMAKE_SOURCE_DIR}/src/lib/modules/${module}/${module}.tex)
		set(MODULE_INCLUDES "${MODULE_INCLUDES}\n\\subsection{The \\texttt{${module}}}\n\\input{../src/lib/modules/${module}/${module}.tex}\n")
	endif()
endforeach()

configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/module_list.tex.in ${CMAKE_CURRENT_SOURCE_DIR}/module_list.tex )

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
	set(TEX_DIR ${CMAKE_CURRENT_SOURCE_DIR})
	set(PDF_OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/manual.pdf)
	set(BBL_OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/manual.bbl)
	add_custom_target( manual-pdf-first
		COMMAND ${PDFLATEX_COMPILER}
		-output-directory=${CMAKE_CURRENT_BINARY_DIR} manual.tex
		WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
	)
	add_custom_target( manual-pdf-second
		COMMAND ${PDFLATEX_COMPILER}
		-output-directory=${CMAKE_CURRENT_BINARY_DIR} manual.tex
		WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
		DEPENDS manual-pdf-first
	)
	add_custom_target( manual-bib-copy
		COMMAND cp ${CMAKE_CURRENT_SOURCE_DIR}/*.bib ${CMAKE_CURRENT_BINARY_DIR}/
		DEPENDS manual-pdf-second
	)
	add_custom_target( manual-bib
		COMMAND ${BIBTEX_COMPILER}
		manual.aux
		WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
		DEPENDS manual-bib-copy
	)
	add_custom_target( manual-pdf-third
		COMMAND ${PDFLATEX_COMPILER}
		-output-directory=${CMAKE_CURRENT_BINARY_DIR} manual.tex
		WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
		DEPENDS manual-bib
	)
	add_custom_target( manual
		COMMAND mv ${PDF_OUTPUT} ${CMAKE_CURRENT_BINARY_DIR}/manual_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
		DEPENDS manual-pdf-third
	)
	add_custom_target( manual-bib-cleanup
		COMMAND rm ${CMAKE_CURRENT_BINARY_DIR}/*.bib ${CMAKE_CURRENT_BINARY_DIR}/*.aux ${CMAKE_CURRENT_BINARY_DIR}/*.bbl ${CMAKE_CURRENT_BINARY_DIR}/*.out ${CMAKE_CURRENT_BINARY_DIR}/*.toc
		DEPENDS manual
	)
endif( MANUAL_PDFLATEX )
