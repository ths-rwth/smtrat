/**
 * @file IncWidthModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2015-06-29
 * Created on 2015-06-29.
 */

#include "IncWidthModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IncWidthModule<Settings>::IncWidthModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        mHalfOfCurrentWidth( Settings::half_of_start_width ),
        mVariableShifts(),
        mVarBounds()
    {}

    /**
     * Destructor.
     */

    template<class Settings>
    IncWidthModule<Settings>::~IncWidthModule()
    {}

    template<class Settings>
    bool IncWidthModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( mVarBounds.addBound( _subformula->formula().constraint(), _subformula->formula() ) )
        {
            reset();
        }
        return !mVarBounds.conflicting(); // This should be adapted according to your implementation.
    }

    template<class Settings>
    void IncWidthModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( mVarBounds.removeBound( _subformula->formula().constraint(), _subformula->formula() ) )
        {
            reset();
        }
    }

    template<class Settings>
    void IncWidthModule<Settings>::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            getBackendsModel();
            for( auto& ass : mModel )
            {
                auto varShiftIter = mVariableShift.find( ass.first.asVariable() );
                assert( varShiftIter != mVariableShift.end() );
//                Poly shiftedAssignment = varShiftIter->second.substitute( varShiftIter->first, ass.second.asSqrtEx().constantPart().constantPart() );
//                assert( shiftedAssignment.isConstant() );
                
            }
        }
    }

    template<class Settings>
    Answer IncWidthModule<Settings>::checkCore( bool _full )
    {
        // Your code.
        return Unknown; // This should be adapted according to your implementation.
    }
    
    template<class Settings>
    void IncWidthModule<Settings>::reset()
    {
        clearPassedFormula();
        mVariableShifts.clear();
        mHalfOfCurrentWidth = Settings::half_of_start_width;
    }
}