#include "WrapperExternal.h"
#include <iostream>

namespace smtrat {

    void WrapperExternal::setLemmaLevel(int _level)
    {
        assert(_level >= 0 && _level <= 2);
        LemmaLevel level = static_cast<LemmaLevel>(_level);
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Set lemma level: " << level);
        solver->setLemmaLevel(level);
    }

    std::size_t WrapperExternal::parseFormula(const char* input, char* buffer, std::size_t bufferSize)
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Parse: " << input);
        FormulaT parseResult = parser.formula(input);
        std::ostringstream stream;
        stream << parseResult;
        return copyResult(stream, buffer, bufferSize);
    }

    bool WrapperExternal::inform(const char* _constraint, const char*
#ifdef LOGGING
        _name
#endif
    )
    {
        FormulaT constraint = parser.formula(_constraint);
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Informed: " << constraint << "(" << _name << ")");
        //TODO Matthias: set name
        return solver->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula, const char* 
#ifdef LOGGING
        _name
#endif
    )
    {
        FormulaT subformula = parser.formula(_subformula);
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Added: " << subformula << "(" << _name << ")");
        //TODO Matthias: set name
        return solver->add(subformula);
    }

    std::size_t WrapperExternal::addWithVariables(const char* _subformula, const char* 
#ifdef LOGGING
        _name
#endif
        , char* buffer, std::size_t bufferSize)
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        //Add formula
        FormulaT subformula = parser.formula(_subformula);
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Added: " << subformula << "(" << _name << ")");
        //TODO Matthias: set name
        solver->add(subformula);
        //Return variables
        std::ostringstream stream;
        stream << subformula << std::endl;
        carl::Variables variables;
        subformula.booleanVars(variables);
        for (carl::Variables::iterator iter = variables.begin(); iter != variables.end(); iter++)
        {
            stream << *iter << std::endl;
        }
        return copyResult(stream, buffer, bufferSize);
    }

    void WrapperExternal::addInformationRelevantFormula(const char* _formula)
    {
        FormulaT formula = parser.formula(_formula);
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Added informationRelevantFormula: " << formula);
        return solver->addInformationRelevantFormula(formula);
    }

    void WrapperExternal::clearInformationRelevantFormula()
    {
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Clear informationRelevantFormula");
        return solver->clearInformationRelevantFormula();
    }

    unsigned WrapperExternal::check()
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

    void WrapperExternal::reset()
    {
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "Reset");
        return solver->reset();
    }

    std::size_t WrapperExternal::infeasibleSubsets(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "infeasibleSubsets");
        std::vector<FormulaSetT> infeasibleSubsets = solver->infeasibleSubsets();
        std::ostringstream stream;
        for (const FormulaSetT& subset : infeasibleSubsets)
        {
            stream << subset << std::endl;
        }
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::getModelEqualities(char* buffer, std::size_t bufferSize) const
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

    std::size_t WrapperExternal::model(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "model");
        Model model = solver->model();
        std::ostringstream stream;
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::allModels(char* buffer, std::size_t bufferSize) const
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

    std::size_t WrapperExternal::lemmas(char* buffer, std::size_t bufferSize) const
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

    std::size_t WrapperExternal::formula(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        // TODO Matthias: fix linker error and activate again
        //ModuleInput formula = solver->formula();
        std::ostringstream stream;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "formula()");
        SMTRAT_LOG_NOTIMPLEMENTED();
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::getAssignmentString(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "assignmentString");
        std::ostringstream stream;
        solver->printAssignment();
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::getAssertionsString(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "assertionsString");
        std::ostringstream stream;
        solver->printAssertions();
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::getInfeasibleSubsetString(char* buffer, std::size_t bufferSize) const
    {
        if (tryCopyOld(buffer, bufferSize))
            return 0;
        SMTRAT_LOG_DEBUG("smtrat.wrapper", "infeasibleSubsetString");
        std::ostringstream stream;
        solver->printInfeasibleSubset(stream);
        return copyResult(stream, buffer, bufferSize);
    }

    std::size_t WrapperExternal::copyResult(const std::ostringstream& stream, char* buffer, std::size_t bufferSize) const
    {
        lastBuffer = stream.str();
        if (lastBuffer.size() > bufferSize) {
            return lastBuffer.size() + 1;
        } else {
            assert(lastBuffer.size() < bufferSize);
#ifdef __WIN
            strcpy_s(buffer, bufferSize, lastBuffer.c_str());
#else
            strncpy(buffer, lastBuffer.c_str(), bufferSize);
#endif
            lastBuffer = "";
            return 0;
        }
    }

    bool WrapperExternal::tryCopyOld(char* buffer, std::size_t bufferSize) const
    {
        if (lastBuffer != "")
        {
            assert(lastBuffer.size() < bufferSize);
#ifdef __WIN
            strcpy_s(buffer, bufferSize, lastBuffer.c_str());
#else
            strncpy(buffer, lastBuffer.c_str(), bufferSize);
#endif
            lastBuffer = "";
            return true;
        }
        return false;
    }
}
