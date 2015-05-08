/**
 * @file testtestModule.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-05-08
 * Created on 2015-05-08.
 */

#include "testtestModule.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    testtestModule::testtestModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
        Module( _type, _formula, _conditionals, _manager ) 
    {}

    /**
     * Destructor.
     */

    testtestModule::~testtestModule()
    {}


    bool testtestModule::informCore( const FormulaT& _constraint )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    void testtestModule::init()
    {}

    bool testtestModule::addCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
        return true; // This should be adapted according to your implementation.
    }

    void testtestModule::removeCore( ModuleInput::const_iterator _subformula )
    {
        // Your code.
    }

    void testtestModule::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            // Your code.
        }
    }

    Answer testtestModule::checkCore( bool _full )
    {
        // Your code.
        return Unknown; // This should be adapted according to your implementation.
    }
}