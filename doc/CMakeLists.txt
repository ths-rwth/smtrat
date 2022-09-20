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

# Check if LaTeX is available
find_package(LATEX COMPONENTS PDFLATEX BIBTEX)
if(NOT LATEX_FOUND)
	message(STATUS "LaTeX is not available, parts of building the documentation may not work as expected.")
endif()

# Paths for documentations
set(OUTPUT_DIR ${PROJECT_BINARY_DIR}/doc)

# Prepare markdown content
add_subdirectory(markdown)
# Prepare pictures
add_subdirectory(pictures)

# Collect all sources for proper dependencies
set(CODE_SOURCE_DIR ${PROJECT_SOURCE_DIR}/src)
file(GLOB_RECURSE COMMON_SOURCES "${CODE_SOURCE_DIR}/**/*.md")
file(GLOB_RECURSE CODE_SOURCES "${CODE_SOURCE_DIR}/**/*.cpp" "${CODE_SOURCE_DIR}/**/*.h" "${CODE_SOURCE_DIR}/**/*.tpp")
file(GLOB_RECURSE MARKDOWN_SOURCES "${PROJECT_SOURCE_DIR}/doc/*" "${PROJECT_SOURCE_DIR}/doc/markdown/**")

# Configure configs
configure_file(apidoc-html/doxygen.conf.in ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf)
configure_file(apidoc-pdf/doxygen.conf.in ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf)
configure_file(manual/doxygen.conf.in ${OUTPUT_DIR}/config-manual/doxygen.conf)

# Build html apidoc
add_custom_command(
	OUTPUT ${OUTPUT_DIR}/apidoc-html/index.html
	COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf
	DEPENDS ${OUTPUT_DIR}/config-apidoc-html/doxygen.conf ${CODE_SOURCES} ${COMMON_SOURCES} ${MARKDOWN_SOURCES}
)
add_custom_target(doc-apidoc-html
	DEPENDS ${OUTPUT_DIR}/apidoc-html/index.html
	DEPENDS doc-pictures
)

# Build pdf apidoc
add_custom_command(
	OUTPUT ${OUTPUT_DIR}/apidoc-pdf/refman.tex
	COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf
	DEPENDS ${OUTPUT_DIR}/config-apidoc-pdf/doxygen.conf ${COMMON_SOURCES} ${CODE_SOURCES} ${MARKDOWN_SOURCES}
)
add_custom_target(doc-apidoc-pdf
	COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex || echo "done" # cat refman.log
	COMMAND ${BIBTEX_COMPILER} refman || /bin/true
	COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex || echo "done" # cat refman.log
	COMMAND cp ${OUTPUT_DIR}/apidoc-pdf/refman.pdf ${OUTPUT_DIR}/doc_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
	WORKING_DIRECTORY ${OUTPUT_DIR}/apidoc-pdf
	DEPENDS ${OUTPUT_DIR}/apidoc-pdf/refman.tex
	DEPENDS doc-pictures
)

# Build manual
add_custom_command(
	OUTPUT ${OUTPUT_DIR}/manual/refman.tex
	COMMAND Doxygen::doxygen ${OUTPUT_DIR}/config-manual/doxygen.conf
	DEPENDS ${OUTPUT_DIR}/config-manual/doxygen.conf ${COMMON_SOURCES} ${MARKDOWN_SOURCES}
)
add_custom_target(doc-manual
	COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex || cat refman.log 
	COMMAND ${BIBTEX_COMPILER} refman || /bin/true
	COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode refman.tex || cat refman.log
	COMMAND cp ${OUTPUT_DIR}/manual/refman.pdf ${OUTPUT_DIR}/manual_${PROJECT_NAME}-${PROJECT_VERSION_LIB}.pdf
	WORKING_DIRECTORY ${OUTPUT_DIR}/manual
	DEPENDS ${OUTPUT_DIR}/manual/refman.tex
	DEPENDS doc-pictures
)

# umbrella target for the whole documentation
add_custom_target(doc)
add_dependencies(doc doc-apidoc-html)
add_dependencies(doc doc-apidoc-pdf)
add_dependencies(doc doc-manual)