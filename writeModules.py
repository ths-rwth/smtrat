import sys
import os
moduleName = sys.argv[1]

moduleDirectory = 'src/lib/modules/' + moduleName
if not os.path.isdir(moduleDirectory):
   os.makedirs(moduleDirectory)

cmakeContent = '\n\
BeginDefineModule()\n\
ModuleMainHeader({0}/{0}.h)\n\
FILE(GLOB_RECURSE sources *.cpp)\n\
foreach(src ${sources})\n\
    AddModuleSource(${src})\n\
endforeach()\n\
ModuleName({0})\n\
ModuleClass({0})\n\
ModuleVersion(0 0 1)\n\
EndDefineModule(moduleEnabled)\n\
\n\
if(${{moduleEnabled}})\n\
    # do something\n\
endif()'.format(moduleName)

headerContent = '/*\n\
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\n\
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\n\
 *\n\
 * This file is part of SMT-RAT.\n\
 *\n\
 * SMT-RAT is free software: you can redistribute it and/or modify\n\
 * it under the terms of the GNU General Public License as published by\n\
 * the Free Software Foundation, either version 3 of the License, or\n\
 * (at your option) any later version.\n\
 *\n\
 * SMT-RAT is distributed in the hope that it will be useful,\n\
 * but WITHOUT ANY WARRANTY; without even the implied warranty of\n\
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n\
 * GNU General Public License for more details.\n\
 *\n\
 * You should have received a copy of the GNU General Public License\n\
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\n\
 *\n\
 */\n\
/**\n\
 * @file {0}.h\n\
 * @author YOUR NAME <YOUR EMAIL ADDRESS>\n\
 *\n\
 * @version DATE\n\
 * Created on DATE.\n\
 */\n\
\n\
#pragma once\n\
\n\
#include "../../Module.h"\n\
\n\
namespace smtrat\n\
{{\n\
    class {0} : public Module\n\
    {{\n\
        private:\n\
            // Members.\n\
        public:\n\
            {0}( ModuleType _type, const Formula* const, RuntimeSettings*, Conditionals&, Manager* const = NULL );\n\
\n\
            ~{0}();\n\
\n\
            // Main interfaces.\n\
            bool inform( const Constraint* const );\n\
            bool assertSubformula( Formula::const_iterator );\n\
            void removeSubformula( Formula::const_iterator );\n\
            void updateModel();\n\
            Answer isConsistent();\n\
    }};\n\
}}'.format(moduleName)    

sourceContent = '/*\n\
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox\n\
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges\n\
 *\n\
 * This file is part of SMT-RAT.\n\
 *\n\
 * SMT-RAT is free software: you can redistribute it and/or modify\n\
 * it under the terms of the GNU General Public License as published by\n\
 * the Free Software Foundation, either version 3 of the License, or\n\
 * (at your option) any later version.\n\
 *\n\
 * SMT-RAT is distributed in the hope that it will be useful,\n\
 * but WITHOUT ANY WARRANTY; without even the implied warranty of\n\
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n\
 * GNU General Public License for more details.\n\
 *\n\
 * You should have received a copy of the GNU General Public License\n\
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.\n\
 *\n\
 */\n\
/**\n\
 * File:   {0}.cpp\n\
 * @author YOUR NAME <YOUR EMAIL ADDRESS>\n\
 *\n\
 * @version DATE\n\
 * Created on DATE.\n\
 */\n\
\n\
#include "{0}.h"\n\
\n\
namespace smtrat\n\
{{\n\
    /**\n\
     * Constructors.\n\
     */\n\
\n\
    {0}::{0}( ModuleType _type, const Formula* const _formula, RuntimeSettings* settings, Conditionals& _conditionals, Manager* const _manager ):\n\
        Module( _type, _formula, _conditionals, _manager )\n\
    {{\n\
    }}\n\
\n\
    /**\n\
     * Destructor.\n\
     */\n\
\n\
    {0}::~{0}()\n\
    {{\n\
    }}\n\
\n\
    /**\n\
     * Main interfaces.\n\
     */\n\
\n\
    /**\n\
     * Informs this module about the existence of the given constraint, which means\n\
     * that it could be added in the future.\n\
     *\n\
     * @param _constraint The constraint to inform about.\n\
     * @return False, if the it can be determined that the constraint itself is conflicting;\n\
     *          True,  otherwise.\n\
     */\n\
    bool {0}::inform( const Constraint* const _constraint )\n\
    {{\n\
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.\n\
        // Your code.\n\
        return _constraint->isConsistent() != 0;\n\
    }}\n\
\n\
    /**\n\
     * Add the subformula of the received formula at the given position to the considered ones of this module.\n\
     *\n\
     * @param _subformula The position of the subformula to add.\n\
     * @return False, if it is easy to decide whether the subformula at the given position is unsatisfiable;\n\
     *          True,  otherwise.\n\
     */\n\
    bool {0}::assertSubformula( Formula::const_iterator _subformula )\n\
    {{\n\
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.\n\
        // Your code.\n\
        return true; // This should be adapted according to your implementation.\n\
    }}\n\
\n\
    /**\n\
     * Removes the subformula of the received formula at the given position to the considered ones of this module.\n\
     * Note that this includes every stored calculation which depended on this subformula.\n\
     *\n\
     * @param _subformula The position of the subformula to remove.\n\
     */\n\
    void {0}::removeSubformula( Formula::const_iterator _subformula )\n\
    {{\n\
        // Your code.\n\
        Module::removeSubformula( _subformula ); // This must be invoked at the end of this method.\n\
    }}\n\
\n\
    /**\n\
     * Updates the current assignment into the model.\n\
     * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.\n\
     */\n\
    void {0}::updateModel()\n\
    {{\n\
        mModel.clear();\n\
        if( solverState() == True )\n\
        {{\n\
            // Your code.\n\
        }}\n\
    }}\n\
\n\
    /**\n\
     * Checks the received formula for consistency.\n\
     */\n\
    Answer {0}::isConsistent()\n\
    {{\n\
        // Your code.\n\
        return Unknown; // This should be adapted according to your implementation.\n\
    }}\n\
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


