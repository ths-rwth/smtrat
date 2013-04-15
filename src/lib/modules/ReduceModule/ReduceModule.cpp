 
 #include "ReduceModule.h" 
 
 namespace smtrat 
 { 
 ReduceModule::ReduceModule( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Manager* const _tsManager ) 
     : 
     Module( _type, _formula, _tsManager ) 
     { 
  
     } 
  
     ReduceModule::~ReduceModule(){} 
 
     /** 
      * Adds a constraint to this module. 
      * 
      * @param _subformula The constraint to add to the already added constraints.  
      * @return true 
      */ 
     bool ReduceModule::assertSubformula( Formula::const_iterator _subformula )  
     { 
         Module::assertSubformula( _subformula ); 
         return true; 
     }
 
     /** 
      * Checks the so far received constraints for consistency.
      */ 
     Answer ReduceModule::isConsistent() 
     { 
 	mSolverState = runBackends(); 
 	if( mSolverState == False ) 
 	{ 
 	    getInfeasibleSubsets(); 
 	} 
         return mSolverState; 
     } 
 
     /** 
      * Removes a everything related to a sub formula of the received formula. 
      * 
      * @param _subformula The sub formula of the received formula to remove. 
      */ 
     void ReduceModule::removeSubformula( Formula::const_iterator _subformula ) 
     { 
         Module::removeSubformula( _subformula ); 
     }
 }