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
        return manager->inform(constraint);
    }

    bool WrapperExternal::add(const char* _subformula)
    {
        carl::parser::Parser<Poly> parser;
        FormulaT subformula = parser.formula(_subformula);
        carl::Variables vars;
        subformula.booleanVars(vars);
        for (auto it = vars.begin(); it != vars.end(); ++it) {
            manager->quantifierManager().addUnquantifiedVariable(*it);
        }
        std::cout << "Added: " << subformula << std::endl;
        return manager->add(subformula);
    }

    int WrapperExternal::check()
    {
        return manager->check();
    }

    void WrapperExternal::push()
    {
        manager->push();
    }

    bool WrapperExternal::pop()
    {
        return manager->pop();
    }

    void WrapperExternal::infeasibleSubsets(char* bufferInfeasibleSubsets, int bufferSize) const
    {
        std::vector<FormulasT> infeasibleSubsets = manager->infeasibleSubsets();
        //TODO convert infeasibleSubsets into bufferInfeasibleSubsets
    }

    void WrapperExternal::getModelEqualities(char* bufferModelEqualities, int bufferSize) const
    {
        std::list<std::vector<carl::Variable>> modelEqualities = manager->getModelEqualities();
        //TODO convert modelEqualities into bufferModelEqualities
    }

    void WrapperExternal::model(char* bufferModel, int bufferSize) const
    {
        Model model = manager->model();
        //TODO convert model into bufferModel
    }

    void WrapperExternal::lemmas(char* bufferLemmas, int bufferSize) const
    {
        std::vector<FormulaT> lemmas = manager->lemmas();
        //TODO convert lemmas into bufferLemmas
    }

    void WrapperExternal::formula(char* bufferFormula, int buffersize) const
    {
        //ModuleInput formula = manager->formula();
        //TODO convert formula into bufferFormula
    }

    void WrapperExternal::getAssignmentString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        manager->printAssignment(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

    void WrapperExternal::getAssertionsString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        manager->printAssertions(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

    void WrapperExternal::getInfeasibleSubsetString(char* buffer, int bufferSize) const
    {
        std::ostringstream stream;
        manager->printAssignment(stream);
        // Copy result in buffer for external program
        strcpy_s(buffer, bufferSize, stream.str().c_str());
    }

}
