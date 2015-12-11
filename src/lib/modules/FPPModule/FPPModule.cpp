/**
 * @file FPPModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

#include "FPPModule.h"

namespace smtrat
{
    template<class Settings>
    FPPModule<Settings>::FPPModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        PModule( _formula, _conditionals, _manager ),
#ifdef SMTRAT_DEVOPTION_Statistics
		mStatistics(SettingsType::moduleName),
#endif
        mIterations( 0 ),
        mFormulaAfterPreprocessing( carl::FormulaType::TRUE ),
        mPreprocessor()
    {}

    template<class Settings>
    FPPModule<Settings>::~FPPModule()
    {}

    template<class Settings>
    bool FPPModule<Settings>::informCore( const FormulaT& _constraint )
    {
        return mPreprocessor.inform( _constraint );
    }

    template<class Settings>
    void FPPModule<Settings>::init()
    {
    }

    template<class Settings>
    bool FPPModule<Settings>::addCore( ModuleInput::const_iterator )
    {
        return true;
    }

    template<class Settings>
    void FPPModule<Settings>::removeCore( ModuleInput::const_iterator )
    {
    }

    template<class Settings>
    void FPPModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() != UNSAT )
        {
            const Model& preprocessorModel = mPreprocessor.model();
            Module::updateModel();
            for( auto& ass : preprocessorModel )
                mModel[ass.first] = ass.second;
        }
    }

    template<class Settings>
    Answer FPPModule<Settings>::checkCore( bool _full, bool _minimize )
    {
        //if( mIterations > 0 ) // we did a check before hence the result is still stored in the preprocessor
        //    mPreprocessor.pop();
        mIterations = 0;
        Answer ans = UNKNOWN;
        FormulaT formulaBeforePreprocessing = (FormulaT) rReceivedFormula();
        while( Settings::max_iterations < 0 || mIterations < (std::size_t)Settings::max_iterations )
        {
            ++mIterations;
            // call the preprocessing on the current formula
            mPreprocessor.push();
            mPreprocessor.add( formulaBeforePreprocessing );
            ans = mPreprocessor.check( _full ); // @todo: do we need to add the objective function to the preprocessors??
            // preprocessing detects satisfiabilty or unsatisfiability
            if( ans != UNKNOWN ) {
	            mPreprocessor.pop();
                break;
			}
            std::pair<bool,FormulaT> res = mPreprocessor.getInputSimplified();
	        mPreprocessor.pop();
            if( res.first )
            {
				SMTRAT_LOG_INFO("smtrat.fpp", "Formula has been simplified from" << std::endl << formulaBeforePreprocessing << std::endl << "\tto" << std::endl << res.second);
                mFormulaAfterPreprocessing = res.second;
            }
            else
            {
                break;
            }
            // after preprocessing is before preprocessing
            formulaBeforePreprocessing = mFormulaAfterPreprocessing;
        }
        if( ans == UNKNOWN )
        {
            // run the backends on the fix point of the iterative application of preprocessing
            // TODO: make this incremental
            clearPassedFormula();
            addSubformulaToPassedFormula( mFormulaAfterPreprocessing );
            ans = runBackends( _full, _minimize );
        }
        // obtain an infeasible subset, if the received formula is unsatisfiable
        if( ans == UNSAT )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
}

#include "Instantiation.h"
