#include "WrapperExternal.h"
#include <iostream>

namespace smtrat {
	int WrapperExternal::parseFormula(const char* input, char* buffer, int bufferSize)
	{
		FormulaT parseResult = parser.formula(input);
		// Copy result in buffer for external program
		string result = parseResult.toString();
		if (result.size() > bufferSize) {
			return result.size() + 1;
		}
		else {
			assert(result.size() < bufferSize);
			strcpy_s(buffer, bufferSize, result.c_str());
			return 0;
		}
	}

    bool WrapperExternal::inform(const char* _constraint)
    {
        FormulaT constraint = parser.formula(_constraint);
        std::cout << "Informed: " << constraint << std::endl;
        return solver->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula)
    {
        FormulaT subformula = parser.formula(_subformula);
        std::cout << "Added: " << subformula << std::endl;
        return solver->add(subformula);
    }

    int WrapperExternal::check()
    {
        return solver->check();
    }

    void WrapperExternal::push()
    {
		std::cout << "Push" << std::endl;
		solver->push();
    }

    bool WrapperExternal::pop()
    {
		std::cout << "Pop (Not implemented yet)" << std::endl;
		//TODO Matthias: fix failures with pop
		//return solver->pop();
		return true;
    }

    void WrapperExternal::infeasibleSubsets(char* bufferInfeasibleSubsets, int bufferSize) const
    {
        std::vector<FormulasT> infeasibleSubsets = solver->infeasibleSubsets();
        //TODO convert infeasibleSubsets into bufferInfeasibleSubsets
		std::cout << "infeasibleSubsets (Not implemented yet)" << std::endl;
    }

    void WrapperExternal::getModelEqualities(char* bufferModelEqualities, int bufferSize) const
    {
        std::list<std::vector<carl::Variable>> modelEqualities = solver->getModelEqualities();
        //TODO convert modelEqualities into bufferModelEqualities
		std::cout << "getModelEqualities (Not implemented yet)" << std::endl;
	}

    void WrapperExternal::model(char* bufferModel, int bufferSize) const
    {
        Model model = solver->model();
        //TODO convert model into bufferModel
		std::cout << "model (Not implemented yet)" << std::endl;
	}

    void WrapperExternal::lemmas(char* bufferLemmas, int bufferSize) const
    {
        std::vector<FormulaT> lemmas = solver->lemmas();
        //TODO convert lemmas into bufferLemmas
		std::cout << "lemmas (Not implemented yet)" << std::endl;
	}

    void WrapperExternal::formula(char* bufferFormula, int buffersize) const
    {
        //ModuleInput formula = solver->formula();
        //TODO convert formula into bufferFormula
		std::cout << "formula (Not implemented yet)" << std::endl;
	}

    int WrapperExternal::getAssignmentString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssignment(stream);
        // Copy result in buffer for external program
        string result = stream.str();
        if (result.size() > bufferSize) {
            return result.size() + 1;
        }
        else {
            assert(result.size() < bufferSize);
            strcpy_s(buffer, bufferSize, result.c_str());
			return 0;
        }
    }

    int WrapperExternal::getAssertionsString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssertions(stream);
        // Copy result in buffer for external program
        string result = stream.str();
        if (result.size() > bufferSize) {
            return result.size() + 1;
        }
        else {
            assert(result.size() < bufferSize);
            strcpy_s(buffer, bufferSize, result.c_str());
			return 0;
        }
    }

    int WrapperExternal::getInfeasibleSubsetString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printInfeasibleSubset(stream);
        // Copy result in buffer for external program
        string result = stream.str();
        if (result.size() > bufferSize) {
            return result.size() + 1;
        }
        else {
            assert(result.size() < bufferSize);
            strcpy_s(buffer, bufferSize, result.c_str());
			return 0;
        }
    }

}
