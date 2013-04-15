 
 #pragma once 
 
 #include "../../Module.h" 
 
 namespace smtrat 
 { 
     class ReduceModule : public Module 
     { 
         public: 
             ReduceModule( ModuleType, const Formula* const,  RuntimeSettings*, Manager* const _tsManager ); 
 
             virtual ~ReduceModule(); 
 
             // Interfaces. 
             bool assertSubformula( Formula::const_iterator ); 
             Answer isConsistent(); 
             void removeSubformula( Formula::const_iterator ); 
     }; 
 }