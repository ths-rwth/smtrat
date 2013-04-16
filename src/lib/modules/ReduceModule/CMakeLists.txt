# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: CMakeLists.txt                                        #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-04-16                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

BeginDefineModule()
ModuleMainHeader(ReduceModule/ReduceModule.h)
ModuleName(ReduceModule)
ModuleClass(ReduceModule)
ModuleVersion(0 0 1)
EndDefineModule(moduleEnabled)

if(${moduleEnabled})
    include(ExternalProject)
    ExternalProject_Add( libreduce
                         SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/libreduce
                         CONFIGURE_COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/libreduce/src/configure --prefix=<INSTALL_DIR>
                         BUILD_COMMAND ${MAKE}
                         INSTALL_COMMAND "" )
    if(DEFINED ENV{REDUCE_PATH})
        set(REDUCE_PATH "$ENV{REDUCE_PATH}" CACHE PATH "Path to the binary of the computer algebra system Reduce")
    else()
        set(REDUCE_PATH "/usr/bin" CACHE PATH "Path to the binary of the computer algebra system Reduce")
    endif()
    message(STATUS "Reduce path: ${REDUCE_PATH}")
    ExternalProject_Get_Property(libreduce install_dir)
    if(${STATICLIB_SWITCH} STREQUAL "ON")
        set( libraries ${install_dir}/src/libreduce-build/libreduce.so ${libraries} )
    else()
        set( libraries ${install_dir}/src/libreduce-build/libreduce.a ${libraries} )
    endif()

    file(GLOB_RECURSE sources *.cpp)
    set(modulesSources ${modulesSources} ${sources} PARENT_SCOPE)

    configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/ReduceModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/ReduceModule/config.h )
endif()
