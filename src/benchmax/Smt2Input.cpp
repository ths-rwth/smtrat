/**
 * @file   Smt2Input.cpp
 *         Created on April 10, 2013, 5:26 PM
 * @author: Sebastian Junges
 *
 *
 */

#include "Smt2Input.h"

#include <iostream>
#include <fstream>

#ifdef BENCHMAX_USE_SMTPARSER

#include <../src/lib/Formula.h>
#include <../src/solver/parser/Driver.h>
#include <../src/solver/ExitCodes.h>

#include "Stats.h"
#include "BenchmarkStatus.h"

bool Smt2Input::initialized = false;

Smt2Input* Smt2Input::initialize()
{
    if(!initialized)
    {
        return new Smt2Input();
    }
    else
    {
        return NULL;
    }
}

Smt2Input::Smt2Input():
    mInputFormula(NULL),
    mCnfFormula(NULL)
{
    initialized = true;
}

Smt2Input::~Smt2Input()
{
    if(mInputFormula != NULL)
    {
        delete mInputFormula;
    }
    if(mCnfFormula != NULL)
    {
        delete mCnfFormula;
    }
    Formula::mpConstraintPool->clear();
    initialized = false;
}

bool Smt2Input::parseSmtLib(const fs::path& smt2file)
{
    Formula* form = new Formula(smtrat::AND);
    smtrat::Driver driver;

    std::fstream infile(smt2file.string());
    if(!infile.good())
    {
        std::cerr << "Parser could not open file: " << smt2file.string() << std::endl;
        return false;
    }

    driver.parse_stream(infile, smt2file.string());

    // conjoin all assertions by a conjunction
    smtrat::InstructionKey currentInstructionKey;
    smtrat::InstructionValue currentInstructionValue;
    while( driver.getInstruction( currentInstructionKey, currentInstructionValue ) )
    {
        switch( currentInstructionKey )
        {
            case smtrat::PUSHBT:
            {
                break;
            }
            case smtrat::POPBT:
            {
                break;
            }
            case smtrat::ASSERT:
            {
                form->addSubformula( currentInstructionValue.formula );
                break;
            }
            case smtrat::CHECK:
            {
                break;
            }
            case smtrat::GET_ASSIGNMENT:
            {
                break;
            }
            case smtrat::GET_ASSERTS:
            {
                break;
            }
            case smtrat::GET_UNSAT_CORE:
            {
                break;
            }
            default:
            {
                driver.error( "Unknown order!" );
                assert( false );
            }
        }
    }
    
    mInputFormula = form;
    mStatus       = benchmarkStatusFromParser(driver.status());

    return true;
}

bool Smt2Input::extractInputStatistics(Stats* stats)
{
    // For some statistics, we need the cnfed form of the formula.
    if(mCnfFormula == NULL)
    {
        mCnfFormula = new Formula(*mInputFormula);
    }
    Formula::toCNF(*mCnfFormula);

    // Add input statistics.
    stats->addInputStat("status", benchmarkStatusToString(mStatus));
    stats->addInputStat("nrRealVars", mInputFormula->numberOfRealVariables());
    stats->addInputStat("nrBoolVars", mInputFormula->numberOfBooleanVariables());
    stats->addInputStat("maxDegree", Formula::mpConstraintPool->maxDegree());
    stats->addInputStat("nrConstraints", Formula::mpConstraintPool->size());
    stats->addInputStat("nrNonLinearConstraints", Formula::mpConstraintPool->nrNonLinearConstraints());
    stats->addInputStat("nrTseitinVars", mCnfFormula->numberOfBooleanVariables() - mInputFormula->numberOfBooleanVariables());
    stats->addInputStat("isAConjunction", (smtrat::PROP_IS_PURE_CONJUNCTION <= mInputFormula->getPropositions() ? "yes" : "no"));
    stats->addInputStat("containsEquations", (smtrat::PROP_CONTAINS_EQUATION <= mInputFormula->getPropositions() ? "yes" : "no"));
    stats->addInputStat("containsInequalities", (smtrat::PROP_CONTAINS_INEQUALITY <= mInputFormula->getPropositions() ? "yes" : "no"));
    stats->addInputStat("containsStrictEqualities", (smtrat::PROP_CONTAINS_STRICT_INEQUALITY <= mInputFormula->getPropositions() ? "yes" : "no"));
    return true;
}

#endif
