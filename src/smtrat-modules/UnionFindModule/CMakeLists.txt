BeginDefineModule()
ModuleMainHeader(UnionFindModule/UnionFindModule.h)
ModuleName(UnionFindModule)
ModuleVersion(0 0 1)
EndDefineModule()

add_library(immer INTERFACE)
target_include_directories(immer INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/immer>
    $<INSTALL_INTERFACE:/immer>
)
install_libraries(immer)

set(DEPEND-include immer PARENT_SCOPE)
