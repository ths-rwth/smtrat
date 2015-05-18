#include "WrapperExternal.h"
#include "carl/util/stringparser.h"
#include "carl/util/parser/Parser.h"
#include "carl/util/Common.h"
#include <iostream>

namespace smtrat {

    bool WrapperExternal::inform(const char* _constraint)
    {
        carl::parser::Parser<Poly> parser;
        FormulaT constraint = parser.formula(_constraint);
        std::cout << "Informed: " << constraint << std::endl;
        return solver->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula)
    {
        carl::parser::Parser<Poly> parser;
        FormulaT subformula = parser.formula(_subformula);
        carl::Variables vars;
        subformula.booleanVars(vars);
        for (auto it = vars.begin(); it != vars.end(); ++it) {
            solver->quantifierManager().addUnquantifiedVariable(*it);
        }
        std::cout << "Added: " << subformula << std::endl;
        return solver->add(subformula);
    }

    int WrapperExternal::check()
    {
        std::cout << "Checking.." << std::endl;
        int tmp = solver->check();
        std::cout << "Check ended" << std::endl;
        return tmp;
    }

    void WrapperExternal::push()
    {
        solver->push();
    }

    bool WrapperExternal::pop()
    {
        return solver->pop();
    }

    void WrapperExternal::infeasibleSubsets(char* bufferInfeasibleSubsets, int bufferSize) const
    {
        std::vector<FormulasT> infeasibleSubsets = solver->infeasibleSubsets();
        //TODO convert infeasibleSubsets into bufferInfeasibleSubsets
    }

    void WrapperExternal::getModelEqualities(char* bufferModelEqualities, int bufferSize) const
    {
        std::list<std::vector<carl::Variable>> modelEqualities = solver->getModelEqualities();
        //TODO convert modelEqualities into bufferModelEqualities
    }

    void WrapperExternal::model(char* bufferModel, int bufferSize) const
    {
        Model model = solver->model();
        //TODO convert model into bufferModel
    }

    void WrapperExternal::lemmas(char* bufferLemmas, int bufferSize) const
    {
        std::vector<FormulaT> lemmas = solver->lemmas();
        //TODO convert lemmas into bufferLemmas
    }

    void WrapperExternal::formula(char* bufferFormula, int buffersize) const
    {
        //ModuleInput formula = solver->formula();
        //TODO convert formula into bufferFormula
    }

    void WrapperExternal::getAssignmentString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssignment(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

    void WrapperExternal::getAssertionsString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssertions(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

    void WrapperExternal::getInfeasibleSubsetString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        solver->printAssignment(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

}
