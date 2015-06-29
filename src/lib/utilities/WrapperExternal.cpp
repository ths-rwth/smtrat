#include "WrapperExternal.h"
#include <iostream>

namespace smtrat {
	int WrapperExternal::parseFormula(const char* input, char* buffer, int bufferSize)
	{
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Parse: " << input);
		FormulaT parseResult = parser.formula(input);
		std::ostringstream stream;
		stream << parseResult.toString();
		return copyResult(stream, buffer, bufferSize);
	}

    bool WrapperExternal::inform(const char* _constraint, const char* _name)
    {
        FormulaT constraint = parser.formula(_constraint);
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Informed: " << constraint << "(" << _name << ")");
		//TODO Matthias: set name
		return solver->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula, const char* _name)
    {
        FormulaT subformula = parser.formula(_subformula);
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Added: " << subformula << "(" << _name << ")");
		//TODO Matthias: set name
		return solver->add(subformula);
    }

	void WrapperExternal::addInformationRelevantFormula(const char* _formula)
	{
		FormulaT formula = parser.formula(_formula);
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Added informationRelevantFormula: " << formula);
		return solver->addInformationRelevantFormula(formula);
	}

	int WrapperExternal::check()
	{
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Check...");
        return solver->check();
    }

    void WrapperExternal::push()
    {
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Push");
		solver->push();
    }

    bool WrapperExternal::pop()
    {
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "Pop");
		return solver->pop();
    }

    int WrapperExternal::infeasibleSubsets(char* buffer, int bufferSize) const
    {
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "infeasibleSubsets");
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
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "modelEqualities");
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
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "model");
        Model model = solver->model();
		std::ostringstream stream;
		return copyResult(stream, buffer, bufferSize);
	}

	int WrapperExternal::allModels(char* buffer, int bufferSize) const
	{
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "allModels");
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
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "lemmas");
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
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		// TODO Matthias: fix linker error and activate again
        //ModuleInput formula = solver->formula();
        std::ostringstream stream;
		//stream << formula.toString() << std::endl;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "formula()");
		SMTRAT_LOG_NOTIMPLEMENTED();
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getAssignmentString(char* buffer, int bufferSize) const
	{
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "assignmentString");
        std::ostringstream stream;
        solver->printAssignment(stream);
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getAssertionsString(char* buffer, int bufferSize) const
	{
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "assertionsString");
        std::ostringstream stream;
        solver->printAssertions(stream);
		return copyResult(stream, buffer, bufferSize);
	}

    int WrapperExternal::getInfeasibleSubsetString(char* buffer, int bufferSize) const
	{
		if (tryCopyOld(buffer, bufferSize))
			return 0;
		SMTRAT_LOG_DEBUG("smtrat.wrapper", "infeasibleSubsetString");
        std::ostringstream stream;
        solver->printInfeasibleSubset(stream);
		return copyResult(stream, buffer, bufferSize);
    }

	int WrapperExternal::copyResult(const std::ostringstream& stream, char* buffer, int bufferSize) const
	{
		lastBuffer = stream.str();
		if (lastBuffer.size() > bufferSize) {
			return lastBuffer.size() + 1;
		}
		else {
			assert(result.size() < bufferSize);
			strcpy_s(buffer, bufferSize, lastBuffer.c_str());
			lastBuffer = "";
			return 0;
		}
	}

	bool WrapperExternal::tryCopyOld(char* buffer, int bufferSize) const
	{
		if (lastBuffer != "")
		{
			assert(lastBuffer.size() < bufferSize);
			strcpy_s(buffer, bufferSize, lastBuffer.c_str());
			lastBuffer = "";
			return true;
		}
		return false;
	}
}
