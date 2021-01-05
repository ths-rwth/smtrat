set(MIMALLOC_VERSION "1.6.7")

ExternalProject_Add(
	mimalloc-EP
	GIT_REPOSITORY https://github.com/microsoft/mimalloc.git
	GIT_TAG v${MIMALLOC_VERSION}
	CMAKE_ARGS -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> -DCMAKE_BUILD_TYPE=RELEASE # -DMI_OVERRIDE=OFF
	UPDATE_COMMAND ""
)

ExternalProject_Get_Property(mimalloc-EP install_dir)

# add_imported_library(MIMALLOC OBJECT "${install_dir}/lib/mimalloc-1.6/mimalloc.o" "${install_dir}/lib/mimalloc-1.6/include")
add_imported_library(MIMALLOC SHARED "${install_dir}/lib/mimalloc-1.6/libmimalloc.so" "${install_dir}/lib/mimalloc-1.6/include")
# add_imported_library(MIMALLOC STATIC "${install_dir}/lib/mimalloc-1.6/libmimalloc.a" "${install_dir}/lib/mimalloc-1.6/include")


# add_dependencies(MIMALLOC_OBJECT mimalloc-EP)
add_dependencies(MIMALLOC_SHARED mimalloc-EP)
# add_dependencies(MIMALLOC_STATIC mimalloc-EP)
# add_dependencies(resources MIMALLOC_OBJECT MIMALLOC_SHARED MIMALLOC_STATIC)