#include <iostream>

#include "CMakeOptions.h"

namespace smtrat {

struct OptionPrinter {
	std::ostream& os;
	OptionPrinter(std::ostream& os): os(os) {}
	void operator()(const std::string& name, const std::string& value) {
		if (name.at(0) == '_') return;
		if (value.find('\n') == std::string::npos) {
			os << name << " = " << value << std::endl;
		} else {
			os << name << " has multiple lines." << std::endl;
		}
	}
};

void printCMakeOptions(std::ostream& os) {
	OptionPrinter p(os);
	
	p("ADDITIONAL_INCLUDE_DIRS", R"VAR()VAR");
	p("ADDITIONAL_LINK_DIRS", R"VAR()VAR");
	p("BUILD_GUI", R"VAR(OFF)VAR");
	p("BUILD_SOLVER", R"VAR(ON)VAR");
	p("CMAKE_BUILD_TYPE", R"VAR(DEBUG)VAR");
	p("CMAKE_INSTALL_PREFIX", R"VAR(/usr/local)VAR");
	p("CPPUNIT_CFLAGS", R"VAR(CPPUNIT_CFLAGS-NOTFOUND)VAR");
	p("CPPUNIT_CONFIG_EXECUTABLE", R"VAR(CPPUNIT_CONFIG_EXECUTABLE-NOTFOUND)VAR");
	p("CppUnit_FOUND", R"VAR(FALSE)VAR");
	p("DEVELOPER", R"VAR(ON)VAR");
	p("LOGGING", R"VAR(ON)VAR");
	p("LOGGING_CARL", R"VAR(ON)VAR");
	p("SMTRAT_CADSETTING", R"VAR(1)VAR");
	p("SMTRAT_CAD_VARIABLEBOUNDS", R"VAR(ON)VAR");
	p("SMTRAT_DEVOPTION_MeasureTime", R"VAR(ON)VAR");
	p("SMTRAT_DEVOPTION_Statistics", R"VAR(ON)VAR");
	p("SMTRAT_DEVOPTION_Validation", R"VAR(ON)VAR");
	p("SMTRAT_ENABLE_CADModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_CNFerModule", R"VAR(ON)VAR");
	p("SMTRAT_ENABLE_CacheModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_GroebnerModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_ICPModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_IntEqModule", R"VAR(ON)VAR");
	p("SMTRAT_ENABLE_LRAModule", R"VAR(ON)VAR");
	p("SMTRAT_ENABLE_Preprocessing", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_ReduceModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_SATModule", R"VAR(ON)VAR");
	p("SMTRAT_ENABLE_VRWModule", R"VAR(OFF)VAR");
	p("SMTRAT_ENABLE_VSModule", R"VAR(OFF)VAR");
	p("SMTRAT_GROEBNER_Settings", R"VAR(5)VAR");
	p("SMTRAT_IntEq_SETTINGS", R"VAR(1)VAR");
	p("SMTRAT_LRA_Settings", R"VAR(1)VAR");
	p("SMTRAT_SAT_Settings", R"VAR(1)VAR");
	p("SMTRAT_STRAT_Factorization", R"VAR(ON)VAR");
	p("SMTRAT_STRAT_PARALLEL_MODE", R"VAR(OFF)VAR");
	p("SMTRAT_Strategy", R"VAR(NRATSolver)VAR");
	p("SMTRAT_VS_Settings", R"VAR(2346)VAR");
	p("SMTRAT_VS_VARIABLEBOUNDS", R"VAR(ON)VAR");
	p("STATICLIB_SWITCH", R"VAR(OFF)VAR");
	p("USE_BOOST_REGEX", R"VAR(OFF)VAR");
	p("USE_GINAC", R"VAR(OFF)VAR");
	p("carl_DIR", R"VAR(/home/dustin/Desktop/work/carl/build)VAR");
	p("smtrat_DOC_CREATE_PDF", R"VAR(ON)VAR");
}

}
