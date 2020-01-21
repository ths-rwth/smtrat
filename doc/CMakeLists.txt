option(DOC_CREATE_HTML "Create HTML documentation" ON)
option(DOC_CREATE_PDF "Create PDF reference manual" ON)

# Check if doxygen is available
if(NOT TARGET Doxygen::doxygen)
	message(STATUS "Doxygen not available, no documentation can be built.")
	return()
endif()

# Check if dot is available
if(TARGET Doxygen::dot)
	set(DOXYGEN_HAVE_DOT YES)
else(TARGET Doxygen::dot)
	set(DOXYGEN_HAVE_DOT NO)
endif(TARGET Doxygen::dot)

# Paths for documentations
set(OUTPUT_DIR ${PROJECT_BINARY_DIR}/doc)

# Collect all sources for proper dependencies
set(CODE_SOURCE_DIR ${PROJECT_SOURCE_DIR}/src)
file(GLOB_RECURSE CODE_SOURCES "${CODE_SOURCE_DIR}/**/*.cpp" "${CODE_SOURCE_DIR}/**/*.h" "${CODE_SOURCE_DIR}/**/*.tpp" "${CODE_SOURCE_DIR}/**/*.md")

# Configure config for HTML documentation
configure_file(apidoc/doxygen.conf.in ${OUTPUT_DIR}/config-apidoc/doxygen.conf)

# Build html documentation
add_custom_command(
	OUTPUT ${OUTPUT_DIR}/html/index.html
	COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-apidoc/doxygen.conf
	DEPENDS ${OUTPUT_DIR}/config-apidoc/doxygen.conf ${CODE_SOURCES}
)
# Wrapper target to have proper dependencies
add_custom_target(doc-html
	DEPENDS ${OUTPUT_DIR}/html/index.html
)

# Configure targets
find_package(LATEX COMPONENTS PDFLATEX BIBTEX)
if(LATEX_FOUND)
	add_subdirectory(manual)
	
	file(GLOB_RECURSE COMMON_SOURCES "${PROJECT_SOURCE_DIR}/doc/*")
	file(GLOB_RECURSE MANUAL_SOURCES "${PROJECT_SOURCE_DIR}/doc/manual/**")
	# Configure config for Manual
	configure_file(manual/doxygen.conf.in ${OUTPUT_DIR}/config-manual/doxygen.conf)
	# Build latex sources
	add_custom_command(
		OUTPUT ${OUTPUT_DIR}/manual/refman.tex
		COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-manual/doxygen.conf
		DEPENDS ${OUTPUT_DIR}/config-manual/doxygen.conf ${COMMON_SOURCES} ${MANUAL_SOURCES}
	)

	# Build the manual
	set(TEX_DIR ${OUTPUT_DIR}/manual)
	add_custom_target(doc-pdf
		#COMMAND ${PDFLATEX_COMPILER} refman.tex
		COMMAND ${BIBTEX_COMPILER} refman || /bin/true
		COMMAND ${PDFLATEX_COMPILER} refman.tex
		COMMAND cp ${OUTPUT_DIR}/manual/refman.pdf ${OUTPUT_DIR}/doc_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
		WORKING_DIRECTORY ${OUTPUT_DIR}/manual
		DEPENDS ${OUTPUT_DIR}/manual/refman.tex
	)
else(LATEX_FOUND)
	message(STATUS "Did not find pdflatex, no pdf manual can be built.")
	set(DOXYGEN_CREATE_PDF NO)
endif(LATEX_FOUND)

# umbrella target for the whole documentation
add_custom_target(doc)

if(DOC_CREATE_HTML)
	# Build html documentation by default
	add_dependencies(doc doc-html)
endif()
if(DOC_CREATE_PDF)
	# Build pdf documentation by default
	add_dependencies(doc doc-pdf)
endif(DOC_CREATE_PDF)