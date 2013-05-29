# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: src/lib/modules/CADModule/CMakeLists.txt              #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2013-05-29                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

BeginDefineModule()
ModuleMainHeader(CADModule/CADModule.h)
FILE(GLOB_RECURSE sources *.cpp)
foreach(src ${sources})
    AddModuleSource(${src})
endforeach()
ModuleName(CADModule)
ModuleClass(CADModule)
ModuleVersion(0 7 0)
ModuleDefaultEnabled()
EndDefineModule(enabled)

if(${enabled})
    option( SMTRAT_CAD_VARIABLEBOUNDS "CAD using variable bounds" ON )

    # options for the CADModule settings
    set( SMTRAT_CADSETTING "1" CACHE STRING "All SMT features with equation detection optimization" )
    set( SMTRAT_CADSETTING "2" CACHE STRING "Setting 1 w/o SMT features" )
    set( SMTRAT_CADSETTING "3" CACHE STRING "Setting 1 w/o search optimization for inequalities/equation and SMT features (generic CAD setting)" )
    set( SMTRAT_CADSETTING "4" CACHE STRING "All SMT features with optimization for rational samples" )
    set( SMTRAT_CADSETTING "5" CACHE STRING "Setting 1 w/o theory propagation" )
    set( SMTRAT_CADSETTING "6" CACHE STRING "Setting 1 w/o minimal infeasible subset generation" )
    set( SMTRAT_CADSETTING "7" CACHE STRING "Setting 1 w/o projection order optimization" )
    set( SMTRAT_CADSETTING "8" CACHE STRING "Setting 1 with 1-most-degree-vertex MIS heuristic" )
    set( SMTRAT_CADSETTING "9" CACHE STRING "Setting 1 with 2-most-degree-vertices MIS heuristic" )
    set( SMTRAT_CADSETTING_VALUES "1" "2" "3" "4" "5" "6" "7" "8" "9" )
    set_property( CACHE SMTRAT_CADSETTING PROPERTY STRINGS ${SMTRAT_CADSETTING_VALUES} )
    list( FIND SMTRAT_CADSETTING_VALUES ${SMTRAT_CADSETTING} SMTRAT_CADSETTING_INDEX )
    if( ${SMTRAT_CADSETTING_INDEX} EQUAL -1 )
        message( FATAL_ERROR "Option ${SMTRAT_CADSETTING} not supported, valid entries are ${SMTRAT_CADSETTING_VALUES}" )
        set( SMTRAT_CADSETTING_1 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 0 )
        set( SMTRAT_CADSETTING_1 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 1 )
        set( SMTRAT_CADSETTING_2 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 2 )
        set( SMTRAT_CADSETTING_3 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 3 )
        set( SMTRAT_CADSETTING_4 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 4 )
        set( SMTRAT_CADSETTING_5 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 5 )
        set( SMTRAT_CADSETTING_6 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 6 )
        set( SMTRAT_CADSETTING_7 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 7 )
        set( SMTRAT_CADSETTING_8 TRUE )
    elseif( ${SMTRAT_CADSETTING_INDEX} EQUAL 8 )
        set( SMTRAT_CADSETTING_9 TRUE )
    endif()

    configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/CADModule/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/CADModule/config.h )
endif()