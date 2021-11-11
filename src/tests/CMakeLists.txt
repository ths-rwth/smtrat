#find_package(Boost COMPONENTS unit_test_framework REQUIRED)

# add_definitions(-DBOOST_TEST_DYN_LINK)
# 
# include_directories(${CMAKE_SOURCE_DIR}/src
#                     ${CMAKE_SOURCE_DIR}/src/cli
#                     ${CMAKE_BINARY_DIR}/src/cli
# )
# 
# add_subdirectory(cad)
# add_subdirectory(pseudobool)
# add_subdirectory(onecellcad)
# add_subdirectory(nlsat)
# add_subdirectory(mcsat)
# add_subdirectory(mcsatvs)
# add_subdirectory(fourierMotzkinQE)


add_custom_target(all-tests)

set(GTEST_LIBRARIES GTESTCORE_STATIC GTESTMAIN_STATIC pthread dl)

add_library(TestCommon STATIC Common.cpp)
target_link_libraries(TestCommon ${GTEST_LIBRARIES})
add_dependencies(TestCommon resources GTESTCORE_STATIC GTESTMAIN_STATIC)


################################
# Unit Tests
################################

add_subdirectory(smtrat-cadcells)