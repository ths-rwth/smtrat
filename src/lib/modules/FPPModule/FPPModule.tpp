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
        PModule( _type, _formula, _conditionals, _manager )
    {}

    template<class Settings>
    FPPModule<Settings>::~FPPModule()
    {}

    template<class Settings>
    bool FPPModule<Settings>::informCore( const FormulaT& _constraint )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void FPPModule<Settings>::init()
    {}

    template<class Settings>
    bool FPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    template<class Settings>
    void FPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
    }

    template<class Settings>
    void FPPModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            // Your code.
        }
    }

    template<class Settings>
    Answer FPPModule<Settings>::checkCore( bool _full )
    {
        // Your code.
        return Unknown; // This should be adapted according to your implementation.
    }
}