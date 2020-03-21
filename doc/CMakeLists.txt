option(DOC_CREATE_HTML "Create API HTML documentation" ON)
option(DOC_CREATE_PDF "Create API PDF documentation" ON)
option(DOC_CREATE_MANUAL "Create PDF manual" ON)

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

# Build tikz pictures
add_subdirectory(markdown)
add_subdirectory(pictures)

# Collect all sources for proper dependencies
set(CODE_SOURCE_DIR ${PROJECT_SOURCE_DIR}/src)
file(GLOB_RECURSE COMMON_SOURCES "${CODE_SOURCE_DIR}/**/*.md")
file(GLOB_RECURSE CODE_SOURCES "${CODE_SOURCE_DIR}/**/*.cpp" "${CODE_SOURCE_DIR}/**/*.h" "${CODE_SOURCE_DIR}/**/*.tpp")

# Configure config for API HTML documentation
configure_file(apidoc-html/doxygen.conf.in ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf)

# Build html documentation
add_custom_command(
	OUTPUT ${OUTPUT_DIR}/apidoc-html/index.html
	COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf
	DEPENDS ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf ${CODE_SOURCES} ${COMMON_SOURCES}
)
# Wrapper target to have proper dependencies
add_custom_target(doc-html
	DEPENDS ${OUTPUT_DIR}/apidoc-html/index.html
	DEPENDS doc-pictures
)

# Configure targets
find_package(LATEX COMPONENTS PDFLATEX BIBTEX)
if(LATEX_FOUND)
	
	file(GLOB_RECURSE MANUAL_SOURCES "${PROJECT_SOURCE_DIR}/doc/*" "${PROJECT_SOURCE_DIR}/doc/markdown/**")

	# Configure config for api pdf
	configure_file(apidoc-pdf/doxygen.conf.in ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf)
	# Build latex sources
	add_custom_command(
		OUTPUT ${OUTPUT_DIR}/apidoc-pdf/refman.tex
		COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf
		DEPENDS ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf ${COMMON_SOURCES} ${MANUAL_SOURCES}
	)

	# Build the api pdf
	add_custom_target(doc-pdf
		COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex
		COMMAND ${BIBTEX_COMPILER} refman || /bin/true
		COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex
		COMMAND cp ${OUTPUT_DIR}/apidoc-pdf/refman.pdf ${OUTPUT_DIR}/doc_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
		WORKING_DIRECTORY ${OUTPUT_DIR}/apidoc-pdf
		DEPENDS ${OUTPUT_DIR}/apidoc-pdf/refman.tex
		DEPENDS doc-pictures
	)
	
	# Configure config for Manual
	configure_file(manual/doxygen.conf.in ${OUTPUT_DIR}/config-manual/doxygen.conf)
	# Build latex sources
	add_custom_command(
		OUTPUT ${OUTPUT_DIR}/manual/refman.tex
		COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-manual/doxygen.conf
		DEPENDS ${OUTPUT_DIR}/config-manual/doxygen.conf ${COMMON_SOURCES} ${MANUAL_SOURCES}
	)

	# Build the manual
	add_custom_target(doc-manual
		COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex
		COMMAND ${BIBTEX_COMPILER} refman || /bin/true
		COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex
		COMMAND cp ${OUTPUT_DIR}/manual/refman.pdf ${OUTPUT_DIR}/manual_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
		WORKING_DIRECTORY ${OUTPUT_DIR}/manual
		DEPENDS ${OUTPUT_DIR}/manual/refman.tex
		DEPENDS doc-pictures
	)
else(LATEX_FOUND)
	message(STATUS "Did not find pdflatex, no pdf manual can be built.")
	set(DOC_CREATE_PDF NO)
endif(LATEX_FOUND)

# umbrella target for the whole documentation
add_custom_target(doc)

if(DOC_CREATE_HTML)
	# Build api html documentation by default
	add_dependencies(doc doc-html)
endif()
if(DOC_CREATE_PDF)
	# Build api pdf documentation by default
	add_dependencies(doc doc-pdf)
endif(DOC_CREATE_PDF)
if(DOC_CREATE_MANUAL)
	# Build manual by default
	add_dependencies(doc doc-manual)
endif(DOC_CREATE_MANUAL)