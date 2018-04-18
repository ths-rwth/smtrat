set( Boost_Bootstrap_Command )
if( UNIX )
	set( Boost_Bootstrap_Command ./bootstrap.sh )
	set( Boost_b2_Command ./b2 )
elseif( WIN32 )
	set( Boost_Bootstrap_Command ${CMAKE_COMMAND} -E env "VSCMD_START_DIR=<BUILD_DIR>" .\\bootstrap.bat )
	set( Boost_b2_Command b2.exe )
endif()

string(REPLACE "." "_" BOOST_VERSION_FILENAME ${BOOST_VERSION})

ExternalProject_Add(
	Boost-EP
	URL https://sourceforge.net/projects/boost/files/boost/${BOOST_VERSION}/boost_${BOOST_VERSION_FILENAME}.zip/download
	URL_MD5 ${BOOST_ZIPHASH}
	BUILD_IN_SOURCE 1
	DOWNLOAD_NO_PROGRESS 1
	UPDATE_COMMAND ""
	PATCH_COMMAND ""
	CONFIGURE_COMMAND ${Boost_Bootstrap_Command}
	BUILD_COMMAND  ${Boost_b2_Command} -s NO_BZIP2=1 --variant=release headers
	INSTALL_COMMAND ${Boost_b2_Command} -d0 -s NO_BZIP2=1 --variant=release --without-python --without-mpi install --prefix=<INSTALL_DIR>
)

ExternalProject_Get_Property(Boost-EP INSTALL_DIR)

set(shared_libs)
set(static_libs)
foreach(component ${BOOST_COMPONENTS})
	list(APPEND shared_libs "${INSTALL_DIR}/lib/libboost_${component}${DYNAMIC_EXT}")
	list(APPEND static_libs "${INSTALL_DIR}/lib/libboost_${component}${STATIC_EXT}")
endforeach()

add_imported_library(Boost SHARED "${shared_libs}" "${INSTALL_DIR}/include" ${BOOST_COMPONENTS})
add_imported_library(Boost STATIC "${static_libs}" "${INSTALL_DIR}/include" ${BOOST_COMPONENTS})

unset(shared_libs)
unset(static_libs)

add_dependencies(Boost_SHARED Boost-EP)
add_dependencies(Boost_STATIC Boost-EP)
add_dependencies(resources Boost_SHARED Boost_STATIC)
