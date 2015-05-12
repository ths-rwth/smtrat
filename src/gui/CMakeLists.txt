# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#                                                             #
# File: gui/CMakeLists.txt                                    #
#                                                             #
# Project name: SMT-RAT                                       #
# Contact: Florian Corzilius <corzilius@cs.rwth-aachen.de>,   #
#          Ulrich Loup <loup@cs.rwth-aachen.de>               #
# Project sourceforge page: http://smtrat.sourceforge.net/    #
# Development status: beta                                    #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# Version: 2012-11-20                                         #
# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


# GUI settings
# # # # # # # #
set( JAR_NAME "SMT-XRAT" )
set( DOLLAR "$" )

# modify pathes in build.xml
configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/build.xml.in ${CMAKE_CURRENT_BINARY_DIR}/build.xml )
configure_file( ${CMAKE_CURRENT_SOURCE_DIR}/help.html.in ${CMAKE_CURRENT_BINARY_DIR}/help.html )

# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/gui/Config.java.in ${CMAKE_SOURCE_DIR}/src/gui/Config.java )

# use ant to build the gui
add_custom_target( build-gui ALL ant 
                   DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/build.xml
                   DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/help.html
                   COMMENT "Build java-based graphical user interface" )

# use java to run the gui
add_custom_target( run-gui
                   java -jar ${JAR_NAME}.jar
                   WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                   COMMENT "Run java-based graphical user interface" )