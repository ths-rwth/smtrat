option(EXPORT_TO_CMAKE "Export the project to CMake for easy inclusion" ON)

export(EXPORT smtratTargets FILE "${PROJECT_BINARY_DIR}/smtratTargets.cmake")

if(EXPORT_TO_CMAKE)
	# Export the package for use from the build-tree
	# (this registers the build-tree with a global CMake-registry)
	export(PACKAGE smtrat)
endif()
