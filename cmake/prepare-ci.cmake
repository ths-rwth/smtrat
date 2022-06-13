# Misc stuff to setup ci tools

find_package(PythonInterp 3)

if(PYTHONINTERP_FOUND)
	get_target_property(carl_INCLUDE_DIR carl-arith-shared INTERFACE_INCLUDE_DIRECTORIES)
	add_custom_target(.travis.yml)
	add_custom_command(
		TARGET .travis.yml
		BYPRODUCTS ${CMAKE_SOURCE_DIR}/.travis.yml
		COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_SOURCE_DIR}/.ci/travis_generate.py ${carl_INCLUDE_DIR}/../.ci/
		WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/.ci/
	)
else()
	message(STATUS "Did not find python3, target .travis.yml is not available.")
endif()
