/**
 * @file smtratSolver.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 *
 * Created on May 04, 2012, 2:40 PM
 */

#include <iostream>
#include <fstream>
#include <sys/resource.h>
#include "ExitCodes.h"
#include "../lib/config.h"

#include "config.h"
#include "../lib/strategies/config.h"
#include "RuntimeSettingsManager.h"
#include "../lib/solver/Module.h"
#include "../lib/Common.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics


#include "parser/ParserWrapper.h"
#include "../lib/Common.h"
#include <carl/formula/DIMACSExporter.h>
#include <carl/formula/DIMACSImporter.h>

class Executor : public smtrat::parser::InstructionHandler {
	CMakeStrategySolver* solver;
	unsigned exitCode;
	carl::DIMACSExporter<smtrat::Poly> dimacs;
	std::size_t dimacsID = 0;
public:
	bool exportDIMACS = false;
	smtrat::Answer lastAnswer;
	Executor(CMakeStrategySolver* solver) : smtrat::parser::InstructionHandler(), solver(solver) {}
	~Executor() {
	}
	void add(const smtrat::FormulaT& f) {
		if (exportDIMACS) { dimacs(f); return; }
		this->solver->add(f);
		SMTRAT_LOG_DEBUG("smtrat", "Asserting " << f);
	}
	void check() {
		if (exportDIMACS) {
			dimacsID++;
			std::ofstream out("dimacs_" + std::to_string(dimacsID) + ".dimacs");
			out << dimacs << std::endl;
			out.close();
			return;
		}
		this->lastAnswer = this->solver->check();
		switch (this->lastAnswer) {
			case smtrat::Answer::True: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "unsat") {
					error() << "expected unsat, but returned sat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "sat" << std::endl;
					this->exitCode = SMTRAT_EXIT_SAT;
				}
				//if (settingsManager.printModel()) this->solver->printAssignment(std::cout);
				break;
			}
			case smtrat::Answer::False: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "sat") {
					error() << "expected sat, but returned unsat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "unsat" << std::endl;
					this->exitCode = SMTRAT_EXIT_UNSAT;
				}
				break;
			}
			case smtrat::Answer::Unknown: {
				regular() << "unknown" << std::endl;
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			default: {
				error() << "unexpected output!";
				this->exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
				break;
			}
		}
	}
	void declareFun(const carl::Variable&) {
		//if (smtrat::parser::TypeOfTerm::get(var.getType()) == smtrat::parser::ExpressionType::THEORY) {
		//	this->solver->quantifierManager().addUnquantifiedVariable(var);
		//}
	}
	void declareSort(const std::string&, const unsigned&) {
		//error() << "(declare-sort <name> <arity>) is not implemented.";
	}
	void defineSort(const std::string&, const std::vector<std::string>&, const carl::Sort&) {
		//error() << "(define-sort <name> <sort>) is not implemented.";
	}
	void exit() {
	}
	void getAssertions() {
		this->solver->printAssertions(std::cout);
	}
	void getAssignment() {
            if (this->lastAnswer == smtrat::True) {
                smtrat::Model m = this->solver->model();
                this->cleanModel( m );
                std::cout << std::endl << m;
            }
	}
	void getProof() {
		error() << "(get-proof) is not implemented.";
	}
	void getUnsatCore() {
		this->solver->printInfeasibleSubset(std::cout);
	}
	void getValue(const std::vector<carl::Variable>&) {
		error() << "(get-value <variables>) is not implemented.";
	}
	void pop(std::size_t n) {
		this->solver->pop(n);
		if (exportDIMACS) dimacs.clear();
	}
	void push(std::size_t n) {
		for (; n > 0; n--) this->solver->push();
	}
	void reset() {
		this->solver->reset();
	}
	void setLogic(const smtrat::Logic& logic) {
		if (this->solver->logic() != smtrat::Logic::UNDEFINED) {
			error() << "The logic has already been set!";
		} else {
			this->solver->rLogic() = logic;
		}
	}
	unsigned getExitCode() const {
		return this->exitCode;
	}
};

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
unsigned executeFile(const std::string& pathToInputFile, CMakeStrategySolver* solver, const smtrat::RuntimeSettingsManager& settingsManager) {
	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);

	std::ifstream infile(pathToInputFile);
	if (!infile.good()) {
            std::cerr << "Could not open file: " << pathToInputFile << std::endl;
            exit(SMTRAT_EXIT_NOSUCHFILE);
	}
	Executor* e = new Executor(solver);
	if (settingsManager.exportDIMACS()) e->exportDIMACS = true;
	{
		if (!smtrat::parseSMT2File(e, true, infile)) {
            std::cerr << "Parse error" << std::endl;
            delete e;
            exit(SMTRAT_EXIT_PARSERFAILURE);
        }
	}
	if (e->hasInstructions()) e->runInstructions();
	unsigned exitCode = e->getExitCode();
	if( settingsManager.printModel() && e->lastAnswer == smtrat::True )
	{
            smtrat::Model m = solver->model();
            e->cleanModel( m );
            std::cout << std::endl << m;
	}
	delete e;
	return exitCode;
}

void printTimings(smtrat::Manager* solver)
{
    std::cout << "**********************************************" << std::endl;
    std::cout << "*                  Timings                   *" << std::endl;
    std::cout << "**********************************************" << std::endl;
    std::cout << "\t\tAdd \t\tCheck \t (calls) \tRemove" << std::endl;
    for(std::vector<smtrat::Module*>::const_iterator it =  solver->getAllGeneratedModules().begin(); it != solver->getAllGeneratedModules().end(); ++it)
    {
        std::cout << (*it)->moduleName() << ":\t" << (*it)->getAddTimerMS() << "\t\t" << (*it)->getCheckTimerMS() << "\t(" << (*it)->getNrConsistencyChecks() << ")\t\t" << (*it)->getRemoveTimerMS() << std::endl;

    }
    std::cout << "**********************************************" << std::endl;
}

//#include "../lib/datastructures/expression/ExpressionTest.h"

/**
 *
 */
int main( int argc, char* argv[] )
{
	//smtrat::testExpression();
#ifdef LOGGING
	if (!carl::logging::logger().has("smtrat")) {
		carl::logging::logger().configure("smtrat", "smtrat.log");
	}
	if (!carl::logging::logger().has("stdout")) {
		carl::logging::logger().configure("stdout", std::cout);
	}
	carl::logging::logger().filter("smtrat")
		("smtrat", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
	;
	carl::logging::logger().filter("stdout")
		("smtrat", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.parser", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.strategygraph", carl::logging::LogLevel::LVL_DEBUG)
	;
#endif
	SMTRAT_LOG_INFO("smtrat", "Starting smtrat.");
    // This variable will hold the input file.
    std::string pathToInputFile = "";

    // Construct the settingsManager.
    smtrat::RuntimeSettingsManager settingsManager;
    // Introduce the smtrat core settingsObjects to the manager.
    #ifdef SMTRAT_DEVOPTION_Validation
    settingsManager.addSettingsObject( "validation", smtrat::Module::validationSettings );
    #endif
    // Introduce the settings object for the statistics to the manager.
    #ifdef SMTRAT_DEVOPTION_Statistics
    settingsManager.addSettingsObject("stats", smtrat::CollectStatistics::settings);
    #endif

    // Parse command line.
    pathToInputFile = settingsManager.parseCommandline( argc, argv );
    
    #ifdef SMTRAT_DEVOPTION_Statistics
    smtrat::CollectStatistics::settings->setPrintStats( settingsManager.printStatistics() );
    #endif

    // Construct solver.
    CMakeStrategySolver* solver = new CMakeStrategySolver();
	    
    #ifdef SMTRAT_DEVOPTION_Statistics
    //smtrat::CollectStatistics::settings->rOutputChannel().rdbuf( parser.rDiagnosticOutputChannel().rdbuf() );
    #endif
    
    // Introduce the settingsObjects from the modules to the manager.
    //settingsManager.addSettingsObject( settingsObjects );
    //settingsObjects.clear();
	
	
	unsigned exitCode = 0;
	if (settingsManager.readDIMACS()) {
		carl::DIMACSImporter<smtrat::Poly> dimacs(pathToInputFile);
		while (dimacs.hasNext()) {
			solver->add(dimacs.next());
			switch (solver->check()) {
				case smtrat::Answer::True: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case smtrat::Answer::False: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case smtrat::Answer::Unknown: {
					std::cout << "unknown" << std::endl;
					exitCode = SMTRAT_EXIT_UNKNOWN;
					break;
				}
				default: {
					std::cerr << "unexpected output!";
					exitCode = SMTRAT_EXIT_UNEXPECTED_ANSWER;
					break;
				}
			}
			if (dimacs.hasNext()) solver->reset();
		}
	} else {
		// Parse input.
    	exitCode = executeFile(pathToInputFile, solver, settingsManager);
	}

    if( settingsManager.doPrintTimings() )
    {
        printTimings( solver );
    }
    
    #ifdef SMTRAT_DEVOPTION_Statistics
    smtrat::CollectStatistics::collect();
    smtrat::CollectStatistics::print( true );
    #endif
        
    #ifdef SMTRAT_DEVOPTION_Statistics
    // Export statistics.
    smtrat::CollectStatistics::exportXML();
    #endif
    
    
    // Delete the solver and the formula.
    delete solver;

    return (int)exitCode;
}
