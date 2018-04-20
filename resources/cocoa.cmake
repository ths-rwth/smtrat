if (TARGET GMP-EP)
	get_target_property(GMP_LIB GMP_STATIC IMPORTED_LOCATION)
	set(GMP_LIB_ARG "--with-libgmp=${GMP_LIB}")
endif()

ExternalProject_Add(
    CoCoALib-EP
	URL "http://cocoa.dima.unige.it/cocoalib/tgz/CoCoALib-${COCOA_VERSION}.tgz"
	URL_MD5 ${COCOA_TGZHASH}
	DOWNLOAD_NO_PROGRESS 1
	BUILD_IN_SOURCE YES
	CONFIGURE_COMMAND ./configure --prefix=<INSTALL_DIR> --threadsafe-hack ${GMP_LIB_ARG} --with-cxxflags=-Wno-deprecated-declarations\ -fPIC
	BUILD_COMMAND make lib
	INSTALL_COMMAND ${CMAKE_COMMAND} -E touch <SOURCE_DIR>/examples/index.html
	COMMAND ${CMAKE_COMMAND} -E make_directory <INSTALL_DIR>/include
	COMMAND ${CMAKE_COMMAND} -E make_directory <INSTALL_DIR>/lib
	COMMAND ${CMAKE_MAKE_PROGRAM} install
	BUILD_BYPRODUCTS ${CMAKE_BINARY_DIR}/resources/src/CoCoALib-EP/lib/libcocoa${STATIC_EXT}
)

ExternalProject_Get_Property(CoCoALib-EP INSTALL_DIR)

add_imported_library(COCOA SHARED "${INSTALL_DIR}/lib/libcocoa${STATIC_EXT}" "${INSTALL_DIR}/include")
add_imported_library(COCOA STATIC "${INSTALL_DIR}/lib/libcocoa${STATIC_EXT}" "${INSTALL_DIR}/include")

add_dependencies(CoCoALib-EP GMP_STATIC)
add_dependencies(COCOA_SHARED CoCoALib-EP GMPXX_SHARED)
add_dependencies(COCOA_STATIC CoCoALib-EP GMP_STATIC)
add_dependencies(resources COCOA_SHARED COCOA_STATIC)
