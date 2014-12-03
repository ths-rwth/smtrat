/**
 * @file   Smt2Input.h
 *         Created on April 10, 2013, 5:26 PM
 * @author: Sebastian Junges
 * @author: Ulrich Loup
 * @version 2013-04-24
 *
 */

#pragma once

#include "config.h"

#ifdef BENCHMAX_USE_SMTPARSER

#include "BenchmarkStatus.h"

// Forward declarations
namespace smtrat
{
    class Formula;
}
class Stats;

class Smt2Input
{
    protected:
        smtrat::Formula* mInputFormula;
        smtrat::Formula* mCnfFormula;
        BenchmarkStatus  mStatus;

        // As the constraint pool has to be clean, we allow only one instance of smt2input at any time.
        static bool initialized;

        Smt2Input();

    public:
        static Smt2Input* initialize();

        virtual ~Smt2Input();
        bool parseSmtLib(const fs::path& file);
        bool extractInputStatistics(Stats* stats);

        const BenchmarkStatus& getStatus() const
        {
            return mStatus;
        }

        smtrat::Formula* getInputFormula()
        {
            return mInputFormula;
        }

    private:

};

#endif
