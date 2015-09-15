/**
 * @file FPPModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-10
 * Created on 2015-09-10.
 */

namespace smtrat
{
    template<class Settings>
    FPPModule<Settings>::FPPModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        PModule( _type, _formula, _conditionals, _manager ),
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
        while( mIterations < Settings::max_iterations )
        {
            if( mIterations > 0 )
                mPreprocessor.pop();
            ++mIterations;
            // call the preprocessing on the current formula
            mPreprocessor.push();
            mPreprocessor.add( formulaBeforePreprocessing );
            ans = mPreprocessor.check( _full );
            // preprocessing detects satisfiabilty or unsatisfiability
            if( ans != Unknown )
                break;
            std::pair<bool,FormulaT> res = mPreprocessor.getInputSimplified();
            if( res.first )
                mFormulaAfterPreprocessing = res.second;
            else
                break;
            // after preprocessing is before preprocessing
            formulaBeforePreprocessing = mFormulaAfterPreprocessing;
        }
        if( ans == Unknown )
        {
            // run the backends on the fix point of the iterative application of preprocessing
            // TODO: make this incremental
            clearPassedFormula();
            addSubformulaToPassedFormula( mFormulaAfterPreprocessing );
            ans = runBackends( _full );
        }
        // obtain an infeasible subset, if the received formula is unsatisfiable
        if( ans == False )
        {
            mInfeasibleSubsets.clear();
            FormulaSetT infeasibleSubset;
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
            {
                infeasibleSubset.insert( subformula->formula() );
            }
            mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
        }
        return ans;
    }
}