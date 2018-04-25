if(UNIX)
	find_program(M4 m4)
	if(NOT M4)
		message(FATAL_ERROR "Can not build gmp, missing binary for m4")
	endif()
	mark_as_advanced(M4)

	ExternalProject_Add(
		GMP-EP
		URL "https://gmplib.org/download/gmp/gmp-${GMP_VERSION}.tar.bz2"
		URL_MD5 86ee6e54ebfc4a90b643a65e402c4048
		DOWNLOAD_NO_PROGRESS 1
		BUILD_IN_SOURCE YES
		CONFIGURE_COMMAND ./configure --enable-cxx --prefix=<INSTALL_DIR>
	)
elseif(WIN32)
	ExternalProject_Add(
		GMP-EP
		URL "http://mpir.org/mpir-3.0.0.zip"
		URL_MD5 0ac60c2e6e183d401d1f876ca177cdb7
		DOWNLOAD_NO_PROGRESS 1
		CONFIGURE_COMMAND ""
		BUILD_IN_SOURCE YES
		BUILD_COMMAND cd build.vc15
		COMMAND ./msbuild.bat gc dll x64 RELEASE
		COMMAND ./msbuild.bat gc dll x64 DEBUG
		COMMAND ./msbuild.bat gc lib x64 RELEASE
		COMMAND ./msbuild.bat gc lib x64 DEBUG
		INSTALL_COMMAND ${CMAKE_COMMAND} -E make_directory <INSTALL_DIR>/lib
		COMMAND ${CMAKE_COMMAND} -E make_directory <INSTALL_DIR>/include
		COMMAND cp <SOURCE_DIR>/dll/x64/${CMAKE_BUILD_TYPE}/mpir${DYNAMIC_EXT} <INSTALL_DIR>/lib/gmp${DYNAMIC_EXT}
		COMMAND cp <SOURCE_DIR>/dll/x64/${CMAKE_BUILD_TYPE}/mpir${DYNAMIC_EXT} <INSTALL_DIR>/lib/gmpxx${DYNAMIC_EXT}
		COMMAND cp <SOURCE_DIR>/dll/x64/${CMAKE_BUILD_TYPE}/mpir.h <INSTALL_DIR>/include/mpir.h
		COMMAND cp <SOURCE_DIR>/dll/x64/${CMAKE_BUILD_TYPE}/mpirxx.h <INSTALL_DIR>/include/gmpxx.h
		COMMAND cp <SOURCE_DIR>/lib/x64/${CMAKE_BUILD_TYPE}/mpir${STATIC_EXT} <INSTALL_DIR>/lib/gmp${STATIC_EXT}
		COMMAND cp <SOURCE_DIR>/lib/x64/${CMAKE_BUILD_TYPE}/mpirxx${STATIC_EXT} <INSTALL_DIR>/lib/gmpxx${STATIC_EXT}
	)
endif()

ExternalProject_Get_Property(GMP-EP INSTALL_DIR)

add_imported_library(GMP SHARED "${INSTALL_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}gmp${DYNAMIC_EXT}" "${INSTALL_DIR}/include")
add_imported_library(GMP STATIC "${INSTALL_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}gmp${STATIC_EXT}" "${INSTALL_DIR}/include")
add_imported_library(GMPXX SHARED "${INSTALL_DIR}/lib/${CMAKE_SHARED_LIBRARY_PREFIX}gmpxx${DYNAMIC_EXT}" "${INSTALL_DIR}/include")
add_imported_library(GMPXX STATIC "${INSTALL_DIR}/lib/${CMAKE_STATIC_LIBRARY_PREFIX}gmpxx${STATIC_EXT}" "${INSTALL_DIR}/include")

add_dependencies(GMP_SHARED GMP-EP)
add_dependencies(GMP_STATIC GMP-EP)
add_dependencies(GMPXX_SHARED GMP-EP)
add_dependencies(GMPXX_STATIC GMP-EP)
add_dependencies(resources GMP_SHARED GMP_STATIC GMPXX_SHARED GMPXX_STATIC)
