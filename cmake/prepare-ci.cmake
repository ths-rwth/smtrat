# Misc stuff to setup ci tools

find_package(PythonInterp 3 REQUIRED)

add_custom_target(.travis.yml)

message(STATUS "CarL: ${carl_INCLUDE_DIR}")

add_custom_command(
	TARGET .travis.yml
	BYPRODUCTS ${CMAKE_SOURCE_DIR}/.travis.yml
	COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_SOURCE_DIR}/.ci/travis_generate.py ${carl_INCLUDE_DIR}/../.ci/
	WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/.ci/
)
