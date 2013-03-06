#pragma once

#define SMTRAT_PACKAGE_NAME "smtrat"
#define SMTRAT_PROJECT_NAME "SMT-RAT"
#define SMTRAT_VERSION "0.4.0"
#define SMTRAT_WEBSITE "smtrat.sourceforge.net"

/* #undef USE_NSS */
#define USE_GINACRA

// Whether the validation in the module should be enabled
/* #undef SMTRAT_DEVOPTION_Validation */
/* #undef SMTRAT_DEVOPTION_Statistics */
/* #undef SMTRAT_DEVOPTION_MeasureTime */

/* #undef SMTRAT_ENABLE_GroebnerModule */
#define SMTRAT_ENABLE_CADModule
#define SMTRAT_ENABLE_VSModule
/* #undef SMTRAT_ENABLE_Preprocessing */
/* #undef SMTRAT_ENABLE_VRWModule */
#define SMTRAT_ENABLE_LRAModule
/* #undef SMTRAT_ENABLE_CacheModule */

#define SMTRAT_STRAT_Factorization

// Take the GBsetting from cmake
#define GBModuleSettings 

#define CMakeStrategySolver smtrat::NRATSolver 
