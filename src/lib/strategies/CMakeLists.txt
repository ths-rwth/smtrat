set(lib_strategies_src ${lib_strategies_src} strategies/strategyTwo.cpp strategies/${SMTRAT_Strategy}.cpp PARENT_SCOPE )
set(lib_strategies_headers ${lib_strategies_header} strategies/strategyTwo.h strategies/${SMTRAT_Strategy}.h PARENT_SCOPE )
# write config.h
#######################
configure_file( ${CMAKE_SOURCE_DIR}/src/lib/strategies/config.h.in ${CMAKE_SOURCE_DIR}/src/lib/strategies/config.h )

