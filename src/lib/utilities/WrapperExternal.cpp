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
		#ifdef DEBUG_WRAPPER
		std::cout << "Informed: " << constraint << std::endl;
		#endif
		return solver->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula)
    {
        FormulaT subformula = parser.formula(_subformula);
		#ifdef DEBUG_WRAPPER
		std::cout << "Added: " << subformula << std::endl;
		#endif
		return solver->add(subformula);
    }

	void WrapperExternal::addInformationRelevantFormula(const char* _formula)
	{
		FormulaT formula = parser.formula(_formula);
		#ifdef DEBUG_WRAPPER
		std::cout << "Added informationRelevantFormula: " << formula << std::endl;
		#endif
		return solver->addInformationRelevantFormula(formula);
	}

	int WrapperExternal::check()
	{
		#ifdef DEBUG_WRAPPER
		std::cout << "Check..." << std::endl;
		#endif
        return solver->check();
    }

    void WrapperExternal::push()
    {
		#ifdef DEBUG_WRAPPER
		std::cout << "Push" << std::endl;
		#endif
		solver->push();
    }

    bool WrapperExternal::pop()
    {
		std::cout << "Pop (Not yet implemented)" << std::endl;
		//TODO Matthias: fix failures with pop
		//return solver->pop();
		return true;
    }

    int WrapperExternal::infeasibleSubsets(char* buffer, int bufferSize) const
    {
        std::vector<FormulasT> infeasibleSubsets = solver->infeasibleSubsets();
		std::ostringstream stream;
		for (FormulasT subset : infeasibleSubsets)
		{
			stream << subset << std::endl;
		}
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getModelEqualities(char* buffer, int bufferSize) const
    {
        std::list<std::vector<carl::Variable>> modelEqualities = solver->getModelEqualities();
		std::ostringstream stream;
		for (std::vector<carl::Variable> vars : modelEqualities)
		{
			for (carl::Variable var : vars)
			{
				stream << var << ", ";
			}
			stream << std::endl;
		}
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::model(char* buffer, int bufferSize) const
    {
        Model model = solver->model();
		std::ostringstream stream;
		return copyResult(stream, buffer, bufferSize);
	}

	int WrapperExternal::allModels(char* buffer, int bufferSize) const
	{
		std::vector<Model> allModels = solver->allModels();
		std::ostringstream stream;
		for (Model model : allModels)
		{
			stream << model << std::endl;
		}
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::lemmas(char* buffer, int bufferSize) const
    {
        std::vector<FormulaT> lemmas = solver->lemmas();
		std::ostringstream stream;
		for (FormulaT formula : lemmas)
		{
			stream << formula << std::endl;
		}
		return copyResult(stream, buffer, bufferSize);
	}

	int WrapperExternal::formula(char* buffer, int bufferSize) const
    {
		// TODO Matthias: fix linker error and activate again
        //ModuleInput formula = solver->formula();
        std::ostringstream stream;
		//stream << formula.toString() << std::endl;
		stream << "formula() not yet implemented" << std::endl;
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getAssignmentString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssignment(stream);
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getAssertionsString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssertions(stream);
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getInfeasibleSubsetString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printInfeasibleSubset(stream);
		return copyResult(stream, buffer, bufferSize);
    }

	int WrapperExternal::copyResult(const std::ostringstream& stream, char* buffer, int bufferSize) const
	{
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
