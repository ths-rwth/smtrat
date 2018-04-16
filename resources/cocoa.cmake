if (TARGET GMP_EP)
	get_target_property(GMP_LIB GMP_STATIC IMPORTED_LOCATION)
	set(GMP_LIB_ARG "--with-libgmp=${GMP_LIB}")
endif()

ExternalProject_Add(
    CoCoALib-EP
	URL "http://cocoa.dima.unige.it/cocoalib/tgz/CoCoALib-${COCOA_VERSION}.tgz"
	URL_MD5 ${COCOA_TGZHASH}
	DOWNLOAD_NO_PROGRESS 1
	BUILD_IN_SOURCE YES
	CONFIGURE_COMMAND ./configure --threadsafe-hack ${GMP_LIB_ARG} --with-cxxflags=-Wno-deprecated-declarations\ -fPIC
	BUILD_COMMAND make lib
	INSTALL_COMMAND ""
	BUILD_BYPRODUCTS ${CMAKE_BINARY_DIR}/resources/src/CoCoALib-EP/lib/libcocoa${STATIC_EXT}
)

ExternalProject_Get_Property(CoCoALib-EP SOURCE_DIR)

add_imported_library(COCOA SHARED "${SOURCE_DIR}/lib/libcocoa${STATIC_EXT}" "${SOURCE_DIR}/include")
add_imported_library(COCOA STATIC "${SOURCE_DIR}/lib/libcocoa${STATIC_EXT}" "${SOURCE_DIR}/include")

add_dependencies(CoCoALib-EP GMP_STATIC)
add_dependencies(COCOA_SHARED CoCoALib-EP GMPXX_SHARED)
add_dependencies(COCOA_STATIC CoCoALib-EP GMP_STATIC)
add_dependencies(resources COCOA_SHARED COCOA_STATIC)
