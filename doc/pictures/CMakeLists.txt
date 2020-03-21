file(GLOB_RECURSE SOURCES "*.tex")

add_custom_target(
	doc-pictures
)

foreach(FILENAME ${SOURCES})
	file(RELATIVE_PATH TARGET "${CMAKE_CURRENT_LIST_DIR}" "${FILENAME}")
	set(MAIN "${CMAKE_CURRENT_BINARY_DIR}/${TARGET}")
	get_filename_component(MAINWE "${MAIN}" NAME_WE)
	get_filename_component(MAINDIR "${MAIN}" DIRECTORY)
	
	configure_file(template.tex.in "${MAIN}")
	add_custom_target(doc-pictures-${MAINWE}
		COMMAND ${PDFLATEX_COMPILER} -interaction=batchmode ${MAIN}
		COMMAND convert ${MAINDIR}/${MAINWE}.pdf -strip ${MAINDIR}/${MAINWE}.png
		WORKING_DIRECTORY ${MAINDIR}
		DEPENDS ${FILENAME}
	)
	add_dependencies(
		doc-pictures
		doc-pictures-${MAINWE}
	)
endforeach()
