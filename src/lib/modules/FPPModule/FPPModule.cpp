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
        if( solverState() == True )
        {
            const Model& preprocessorModel = mPreprocessor.model();
            Module::updateModel();
            for( auto& ass : preprocessorModel )
                mModel[ass.first] = ass.second;
        }
    }

    template<class Settings>
    Answer FPPModule<Settings>::checkCore( bool _full )
    {
        if( mIterations > 0 ) // we did a check before hence the result is still stored in the preprocessor
            mPreprocessor.pop();
        mIterations = 0;
        Answer ans = Unknown;
        FormulaT formulaBeforePreprocessing = (FormulaT) rReceivedFormula();
        while( Settings::max_iterations < 0 || mIterations < Settings::max_iterations )
        {
            if( mIterations > 0 )
                mPreprocessor.pop();
            ++mIterations;
            // call the preprocessing on the current formula
            mPreprocessor.push();
//            std::cout << "Try to preprocess:" << std::endl;
//            std::cout << formulaBeforePreprocessing << std::endl;
            mPreprocessor.add( formulaBeforePreprocessing );
            ans = mPreprocessor.check( _full );
            // preprocessing detects satisfiabilty or unsatisfiability
            if( ans != Unknown )
                break;
            std::pair<bool,FormulaT> res = mPreprocessor.getInputSimplified();
//                std::cout << "Preprocessing step led to: " << std::endl;
            if( res.first )
            {
                mFormulaAfterPreprocessing = res.second;
//                std::cout << mFormulaAfterPreprocessing << std::endl;
            }
            else
            {
//                std::cout << "No change:" << std::endl;
//                std::cout << mFormulaAfterPreprocessing << std::endl;
                break;
            }
            // after preprocessing is before preprocessing
            formulaBeforePreprocessing = mFormulaAfterPreprocessing;
        }
//        std::cout << "ans after preprocessing: " << ans << std::endl; 
        if( ans == Unknown )
        {
//            std::cout << "ask backends" << std::endl;
            // run the backends on the fix point of the iterative application of preprocessing
            // TODO: make this incremental
            clearPassedFormula();
            addSubformulaToPassedFormula( mFormulaAfterPreprocessing );
            ans = runBackends( _full );
        }
        // obtain an infeasible subset, if the received formula is unsatisfiable
        if( ans == False )
            generateTrivialInfeasibleSubset(); // TODO: compute a better infeasible subset
        return ans;
    }
}

#include "Instantiation.h"
