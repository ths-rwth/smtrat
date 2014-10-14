import sys
import os

def cmakeContent(modName):
  result = '\n\
BeginDefineModule()\n\
ModuleMainHeader('+modName+'/'+modName+'.h)\n\
FILE(GLOB_RECURSE sources *.cpp)\n\
foreach(src ${sources})\n\
    AddModuleSource(${src})\n\
endforeach()\n\
ModuleName('+modName+')\n\
ModuleClass('+modName+')\n\
ModuleVersion(0 0 1)\n\
EndDefineModule(moduleEnabled)\n\
\n\
if(${moduleEnabled})\n\
    # do something\n\
endif()'
  return result

def headerContent(modName,templated):
  result = '/*\n\
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
 * @file '+modName+'.h\n\
 * @author YOUR NAME <YOUR EMAIL ADDRESS>\n\
 *\n\
 * @version DATE\n\
 * Created on DATE.\n\
 */\n\
\n\
#pragma once\n\
\n\
#include "../../solver/Module.h"\n\
\n\
namespace smtrat\n\
{\n\
    class '+modName+' : public Module\n\
    {\n\
        private:\n\
            // Members.\n\
        public:\n\
            '+modName+'( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );\n\
\n\
            ~'+modName+'();\n\
\n\
            // Main interfaces.\n\
            bool inform( const Formula* _constraint );\n\
            bool assertSubformula( ModuleInput::const_iterator _subformula );\n\
            void removeSubformula( ModuleInput::const_iterator _subformula );\n\
            void updateModel() const;\n\
            Answer isConsistent();\n\
    };\n\
}\n'
  if(templated):
    print "F"
    result = result + '#include "IntEqModule.tpp"\n'
    print result
  return result

def sourceContent(modName):
  result = '/*\n\
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
/*\n\
 * File:   '+modName+'.cpp\n\
 * @author YOUR NAME <YOUR EMAIL ADDRESS>\n\
 *\n\
 * @version DATE\n\
 * Created on DATE.\n\
 */\n\
\n\
#include "'+modName+'.h"\n\
\n\
namespace smtrat\n\
{\n\
    /**\n\
     * Constructors.\n\
     */\n\
\n\
    '+modName+'::'+modName+'( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager ):\n\
Module( _type, _formula, _conditionals, _manager ) \n\
    {\n\
    }\n\
\n\
    /**\n\
     * Destructor.\n\
     */\n\
\n\
    '+modName+'::~'+modName+'()\n\
    {\n\
    }\n\
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
    bool '+modName+'::inform( const Formula* _constraint )\n\
    {\n\
        Module::inform( _constraint ); // This must be invoked at the beginning of this method.\n\
        // Your code.\n\
	const Constraint& constraint = _constraint->constraint(); \n\
        return constraint.isConsistent() != 0;\n\
    }\n\
\n\
    /**\n\
     * Add the subformula of the received formula at the given position to the considered ones of this module.\n\
     *\n\
     * @param _subformula The position of the subformula to add.\n\
     * @return False, if it is easy to decide whether the subformula at the given position is unsatisfiable;\n\
     *          True,  otherwise.\n\
     */\n\
    bool '+modName+'::assertSubformula( ModuleInput::const_iterator _subformula )\n\
    {\n\
        Module::assertSubformula( _subformula ); // This must be invoked at the beginning of this method.\n\
        // Your code.\n\
        return true; // This should be adapted according to your implementation.\n\
    }\n\
\n\
    /**\n\
     * Removes the subformula of the received formula at the given position to the considered ones of this module.\n\
     * Note that this includes every stored calculation which depended on this subformula.\n\
     *\n\
     * @param _subformula The position of the subformula to remove.\n\
     */\n\
    void '+modName+'::removeSubformula( ModuleInput::const_iterator _subformula )\n\
    {\n\
        // Your code.\n\
        Module::removeSubformula( _subformula ); // This must be invoked at the end of this method.\n\
    }\n\
\n\
    /**\n\
     * Updates the current assignment into the model.\n\
     * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.\n\
     */\n\
    void '+modName+'::updateModel() const\n\
    {\n\
        mModel.clear();\n\
        if( solverState() == True )\n\
        {\n\
            // Your code.\n\
        }\n\
    }\n\
\n\
    /**\n\
     * Checks the received formula for consistency.\n\
     */\n\
    Answer '+modName+'::isConsistent()\n\
    {\n\
        // Your code.\n\
        return Unknown; // This should be adapted according to your implementation.\n\
    }\n\
}'
  return result



# Print usage information
def printUsage():
  print( "Usage: python "+sys.argv[0]+" m\n" )
  print( "            m: name of the module to create" )
  print( "" )
  print( "Example: python "+sys.argv[0]+" MyModule" )

#
# Parse input.
#
moduleName = ""
templated = False
i = 0
for entry in sys.argv:
  try: 
    if entry == "-h" or entry == "--help":
      printUsage()
      sys.exit(1)
    if entry == "-t":	
      templated = True
    else:
      moduleName = entry
  except ValueError:
    print( "Error:",entry, "should be an appropriate value at position %i." % i )
    printUsage()
    sys.exit(0)
  i += 1
if i != 3:
  print( "Error: Insufficient number of arguments." )
  printUsage()
  sys.exit(0)

moduleDirectory = 'src/lib/modules/' + moduleName
if not os.path.isdir(moduleDirectory):
  os.makedirs(moduleDirectory)

cmakeFile = open(moduleDirectory + '/CMakeLists.txt', 'w')
cmakeFile.write(cmakeContent(moduleName))
cmakeFile.close()

headerFile = open(moduleDirectory + '/' + moduleName + '.h', 'w')
headerFile.write(headerContent(moduleName,templated))
headerFile.close()

if(templated):
  sourceFile = open(moduleDirectory + '/' + moduleName + '.tpp', 'w')
else:
  sourceFile = open(moduleDirectory + '/' + moduleName + '.cpp', 'w')
sourceFile.write(sourceContent(moduleName))
sourceFile.close()

sys.exit(1)

