import sys
import os
moduleName = sys.argv[1]

moduleDirectory = 'src/lib/modules/' + moduleName
if not os.path.isdir(moduleDirectory):
   os.makedirs(moduleDirectory)

cmakeContent = ' \n \
BeginDefineModule() \n \
ModuleMainHeader({0}/{0}.h) \n \
ModuleName({0}) \n \
ModuleClass({0}) \n \
ModuleVersion(0 0 1) \n \
EndDefineModule(moduleEnabled) \n \
\n \
if(${{moduleEnabled}}) \n \
    FILE(GLOB_RECURSE sources *.cpp) \n \
    set(modulesSources ${{modulesSources}} ${{sources}} PARENT_SCOPE) \n \
endif()'.format(moduleName)

headerContent = ' \n \
#pragma once \n \
\n \
#include "../../Module.h" \n \
\n \
namespace smtrat \n \
{{ \n \
    class {0} : public Module \n \
    {{ \n \
        public: \n \
            {0}( ModuleType, const Formula* const,  RuntimeSettings*, Manager* const _tsManager ); \n \
\n \
            virtual ~{0}(); \n \
\n \
            // Interfaces. \n \
            bool assertSubformula( Formula::const_iterator ); \n \
            Answer isConsistent(); \n \
            void removeSubformula( Formula::const_iterator ); \n \
    }}; \n \
}}'.format(moduleName)    

sourceContent = ' \n \
#include "{0}.h" \n \
\n \
namespace smtrat \n \
{{ \n \
{0}::{0}( ModuleType _type, const Formula* const _formula, RuntimeSettings* _settings, Manager* const _tsManager ) \n \
    : \n \
    Module( _type, _formula, _tsManager ) \n \
    {{ \n \
 \n \
    }} \n \
 \n \
    {0}::~{0}(){{}} \n \
\n \
    /** \n \
     * Adds a constraint to this module. \n \
     * \n \
     * @param _subformula The constraint to add to the already added constraints.  \n \
     * @return true \n \
     */ \n \
    bool {0}::assertSubformula( Formula::const_iterator _subformula )  \n \
    {{ \n \
        Module::assertSubformula( _subformula ); \n \
        return true; \n \
    }}\n \
\n \
    /** \n \
     * Checks the so far received constraints for consistency.\n \
     */ \n \
    Answer {0}::isConsistent() \n \
    {{ \n \
	mSolverState = runBackends(); \n \
	if( mSolverState == False ) \n \
	{{ \n \
	    getInfeasibleSubsets(); \n \
	}} \n \
        return mSolverState; \n \
    }} \n \
\n \
    /** \n \
     * Removes a everything related to a sub formula of the received formula. \n \
     * \n \
     * @param _subformula The sub formula of the received formula to remove. \n \
     */ \n \
    void {0}::removeSubformula( Formula::const_iterator _subformula ) \n \
    {{ \n \
        Module::removeSubformula( _subformula ); \n \
    }}\n \
}}'.format(moduleName)

cmakeFile = open(moduleDirectory + '/CMakeLists.txt', 'w')
cmakeFile.write(cmakeContent)
cmakeFile.close()

headerFile = open(moduleDirectory + '/' + moduleName + '.h', 'w')
headerFile.write(headerContent)
headerFile.close()

sourceFile = open(moduleDirectory + '/' + moduleName + '.cpp', 'w')
sourceFile.write(sourceContent)
sourceFile.close()


