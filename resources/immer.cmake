ExternalProject_Add(
    Immer-EP
	GIT_REPOSITORY "https://github.com/arximboldi/immer.git"
	DOWNLOAD_NO_PROGRESS 1
	UPDATE_COMMAND "" # due to https://gitlab.kitware.com/cmake/cmake/issues/17229
	CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> -DCMAKE_INSTALL_LIBDIR=<INSTALL_DIR>/lib -DCMAKE_INSTALL_INCLUDEDIR=<INSTALL_DIR>/include
)

ExternalProject_Get_Property(Immer-EP INSTALL_DIR)

add_imported_library(Immer SHARED "" "${INSTALL_DIR}/include")

add_dependencies(Immer Immer-EP)
# add_dependencies(resources Immer)
