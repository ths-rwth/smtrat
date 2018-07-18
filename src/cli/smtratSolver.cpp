/**
 * @file smtratSolver.cpp
 * @author Florian Corzilius
 * @author Sebastian Junges
 *
 * Created on May 04, 2012, 2:40 PM
 */

#include <iostream>
#include <fstream>
#include "ExitCodes.h"
#include "../lib/config.h"

#include "config.h"
#include "../lib/strategies/config.h"
#include "RuntimeSettingsManager.h"

#ifndef __WIN
#include <sys/resource.h>
#endif
#include "../lib/solver/Module.h"
#include "../lib/Common.h"

#include "../lib/datastructures/unsatcore/UnsatCore.h"

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../lib/utilities/stats/CollectStatistics.h"
#include "lib/utilities/stats/StatisticSettings.h"
#endif //SMTRAT_DEVOPTION_Statistics


#include "parser/ParserWrapper.h"
#include "../lib/Common.h"
#include <carl/formula/parser/DIMACSExporter.h>
#include <carl/formula/parser/DIMACSImporter.h>
#include <carl/formula/parser/OPBImporter.h>
#include <carl/io/SMTLIBStream.h>


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
	void annotateName(const smtrat::FormulaT& f, const std::string& name) {
		SMTRAT_LOG_DEBUG("smtrat", "Naming " << name << ": " << f);
		this->solver->namedFormulas().emplace(name, f);
	}
	void check() {
		smtrat::resource::Limiter::getInstance().resetTimeout();
		if (exportDIMACS) {
			dimacsID++;
			std::ofstream out("dimacs_" + std::to_string(dimacsID) + ".dimacs");
			out << dimacs << std::endl;
			out.close();
			return;
		}
		this->lastAnswer = this->solver->check();
		switch (this->lastAnswer) {
			case smtrat::Answer::SAT: {
                            if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "unsat") {
                                error() << "expected unsat, but returned sat";
                                this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
                            } else {
                                regular() << "sat" << std::endl;
                                if( !this->solver->objectives().empty() )
                                {
                                    regular() << "(objectives" << std::endl;
                                    for( const auto& obj : this->solver->objectives() ) {
                                        smtrat::ModelValue mv = this->solver->optimum(obj.first);
                                        if( mv.isMinusInfinity() || mv.isPlusInfinity() ) {
                                            regular() << " (" << obj.first.toString( false, true ) << " " << carl::toString( mv.asInfinity(), false ) << ")" << std::endl;
                                        } else {
                                            assert( mv.isRational() );
                                            regular() << " (" << obj.first.toString( false, true ) << " " << carl::toString( mv.asRational(), false ) << ")" << std::endl;
                                        }
                                    }
                                    regular() << ")" << std::endl;
                                }
                                this->exitCode = SMTRAT_EXIT_SAT;
                            }
                            //if (settingsManager.printModel()) this->solver->printAssignment(std::cout);
                            break;
			}
			case smtrat::Answer::UNSAT: {
				if (this->infos.has<std::string>("status") && this->infos.get<std::string>("status") == "sat") {
					error() << "expected sat, but returned unsat";
					this->exitCode = SMTRAT_EXIT_WRONG_ANSWER;
				} else {
					regular() << "unsat" << std::endl;
					this->exitCode = SMTRAT_EXIT_UNSAT;
				}
				break;
			}
			case smtrat::Answer::UNKNOWN: {
				regular() << "unknown" << std::endl;
				this->exitCode = SMTRAT_EXIT_UNKNOWN;
				break;
			}
			case smtrat::Answer::ABORTED: {
				regular() << "aborted" << std::endl;
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
	void eliminateQuantifiers(const smtrat::parser::QEQuery& q) {
		regular() << "Eliminating " << q << std::endl;
	}
	void exit() {
	}
	void getAssertions() {
		this->solver->printAssertions(std::cout);
	}
	void getAllModels() {
		if (this->lastAnswer == smtrat::Answer::SAT) {
			for (const auto& m: this->solver->allModels()) {
				regular() << carl::asSMTLIB(m) << std::endl;
			}
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getAssignment() {
            if (this->lastAnswer == smtrat::Answer::SAT) {
                this->solver->printAssignment();
            }
	}
	void getAllAssignments() {
		if (this->lastAnswer == smtrat::Answer::SAT) {
			this->solver->printAllAssignments(std::cout);
		}
	}
	void getModel() {
		if (this->lastAnswer == smtrat::Answer::SAT) {
			regular() << carl::asSMTLIB(this->solver->model()) << std::endl;
		} else {
			error() << "Can only be called after a call that returned sat.";
		}
	}
	void getProof() {
		error() << "(get-proof) is not implemented.";
	}
	void getUnsatCore() {
		//this->solver->printInfeasibleSubset(std::cout);
		smtrat::FormulasT core = computeUnsatCore(this->solver, smtrat::UnsatCoreStrategy::ModelExclusion);
		regular() << "(and";
		for (const auto& f: core) regular() << f << " ";
		regular() << ")" << std::endl;
	}
	void getValue(const std::vector<carl::Variable>&) {
		error() << "(get-value (<variables>)) is not implemented.";
	}
	void addObjective(const smtrat::Poly& p, smtrat::parser::OptimizationType ot) {
            this->solver->addObjective( p, ot == smtrat::parser::OptimizationType::Minimize );
	}
	void pop(std::size_t n) {
            if( n > 1 )
		this->solver->pop(n);
            else
                this->solver->pop();
            if (exportDIMACS) dimacs.clear();
	}
	void push(std::size_t n) {
		for (; n > 0; n--) this->solver->push();
	}
	void reset() {
		smtrat::resource::Limiter::getInstance().reset();
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

bool parseInput(const std::string& pathToInputFile, Executor* e, bool& queueInstructions) {
	if (pathToInputFile == "-") {
		queueInstructions = false;
		SMTRAT_LOG_DEBUG("smtrat", "Starting to parse from stdin");
		return smtrat::parseSMT2File(e, queueInstructions, std::cin);
	}

	std::ifstream infile(pathToInputFile);
	if (!infile.good()) {
		std::cerr << "Could not open file: " << pathToInputFile << std::endl;
		exit(SMTRAT_EXIT_NOSUCHFILE);
	}
	SMTRAT_LOG_DEBUG("smtrat", "Starting to parse " << pathToInputFile);
	return smtrat::parseSMT2File(e, queueInstructions, infile);
}

/**
 * Parse the file and save it in formula.
 * @param pathToInputFile The path to the input smt2 file.
 * @param formula A pointer to the formula object which holds the parsed input afterwards.
 * @param options Save options from the smt2 file here.
 */
unsigned executeFile(const std::string& pathToInputFile, CMakeStrategySolver* solver, const smtrat::RuntimeSettingsManager& settingsManager) {
#ifdef __WIN
//TODO: do not use magical number
#pragma comment(linker, "/STACK:10000000")
#else
	// Increase stack size to the maximum.
	rlimit rl;
	getrlimit(RLIMIT_STACK, &rl);
	rl.rlim_cur = rl.rlim_max;
	setrlimit(RLIMIT_STACK, &rl);
#endif

	Executor* e = new Executor(solver);
	if (settingsManager.exportDIMACS()) e->exportDIMACS = true;
	
	bool queueInstructions = true;
	if (!parseInput(pathToInputFile, e, queueInstructions)) {
		std::cerr << "Parse error" << std::endl;
		delete e;
		exit(SMTRAT_EXIT_PARSERFAILURE);
	}
	if (queueInstructions) {
		if (e->hasInstructions()) {
			SMTRAT_LOG_WARN("smtrat", "Running queued instructions.");
			e->runInstructions();
		} else {
			SMTRAT_LOG_WARN("smtrat", "Did not parse any instructions.");
		}
	}
	unsigned exitCode = e->getExitCode();
	if (e->lastAnswer == smtrat::Answer::SAT) {
		if (settingsManager.printModel()) solver->printAssignment();
		else if (settingsManager.printAllModels()) solver->printAllAssignments(std::cout);
	}
        else if(e->lastAnswer == smtrat::Answer::UNKNOWN) {
            if (settingsManager.printInputSimplified())
            {
                std::stringstream sstream;
                if (solver->logic() != smtrat::Logic::UNDEFINED)
                    sstream << "(set-logic " << solver->logic() << ")" << std::endl;
                smtrat::FormulaT formula = solver->getInputSimplified().second;

                smtrat::Model model = solver->model();
                for (const auto& obj: solver->objectives()) {
                    smtrat::ModelPolynomialSubstitution mps(obj.first);
                    smtrat::ModelValue mv = mps.evaluate(model);
                    formula = smtrat::FormulaT(carl::FormulaType::AND, formula, smtrat::FormulaT(obj.first - mv.asRational(), carl::Relation::EQ));
                }
                sstream << formula.toString( false, 1, "", false, false, true, true ) << std::endl;
                for (const auto& obj: solver->objectives()) {
                    if (obj.second.second) {
                        sstream << "(minimize " << obj.first << ")" << std::endl;
                    } else {
                        sstream << "(maximize " << obj.first << ")" << std::endl;
                    }
                }
                sstream << "(check-sat)" << std::endl;
                if( settingsManager.simplifiedInputFileName() == "" )
                    e->regular() << sstream.str();
                else
                {
                    std::ofstream file;
                    file.open(settingsManager.simplifiedInputFileName());
                    file << sstream.str();
                    file.close();
                }
            }
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
	//carl::logging::logger().formatter("stdout")->printInformation = false;
	carl::logging::logger().filter("smtrat")
		("smtrat", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.preprocessing", carl::logging::LogLevel::LVL_DEBUG)
	;
	carl::logging::logger().filter("stdout")
		("smtrat", carl::logging::LogLevel::LVL_DEBUG)
		("smtrat.module", carl::logging::LogLevel::LVL_INFO)
		("smtrat.parser", carl::logging::LogLevel::LVL_INFO)
		("smtrat.cad", carl::logging::LogLevel::LVL_INFO)
		("smtrat.nlsat.rootindexer", carl::logging::LogLevel::LVL_INFO)
		("smtrat.nlsat.assignmentfinder", carl::logging::LogLevel::LVL_INFO)
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

    if( settingsManager.printStrategy() )
    {
        solver->printStrategyGraph();
        delete solver;
        return (int)SMTRAT_EXIT_SUCCESS;
    }

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
				case smtrat::Answer::SAT: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case smtrat::Answer::UNSAT: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case smtrat::Answer::UNKNOWN: {
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
	} else if (settingsManager.readOPB()) {
		carl::OPBImporter<smtrat::Poly> opb(pathToInputFile);
		SMTRAT_LOG_INFO("smtrat", "Parsing " << pathToInputFile << " using OPB");
		auto input = opb.parse();
		if (!input) {
			SMTRAT_LOG_ERROR("smtrat", "Parsing " << pathToInputFile << " failed.");
			exitCode = SMTRAT_EXIT_UNKNOWN;
		} else {
			SMTRAT_LOG_INFO("smtrat", "Parsed " << input->first);
			SMTRAT_LOG_INFO("smtrat", "with objective " << input->second);
			if (!input->second.isConstant()) {
				solver->addObjective(input->second, true);
			}
			solver->add(input->first);
			switch (solver->check()) {
				case smtrat::Answer::SAT: {
					std::cout << "sat" << std::endl;
					exitCode = SMTRAT_EXIT_SAT;
					break;
				}
				case smtrat::Answer::UNSAT: {
					std::cout << "unsat" << std::endl;
					exitCode = SMTRAT_EXIT_UNSAT;
					break;
				}
				case smtrat::Answer::UNKNOWN: {
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
		}
	} else {
		// Parse input.
		try {
			exitCode = executeFile(pathToInputFile, solver, settingsManager);
		} catch (const std::bad_alloc& e) {
			std::raise(ENOMEM);
		}
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
