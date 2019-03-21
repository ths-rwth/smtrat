add_custom_target(target-dependencies)
add_custom_command(
	TARGET target-dependencies
	BYPRODUCTS dependencies.pdf
	COMMAND cmake --graphviz=targets.dot ../
	COMMAND cat targets.dot | grep -v "strategy" | grep -v "static" | neato -Goverlap=false	-Tpdf -odependencies.pdf
	COMMAND rm targets.dot*
	WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/
)