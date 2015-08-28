import sys
import os
import time

def license(f):
  result = '/**\n\
 * @file ' + f + '\n\
 * @author YOUR NAME <YOUR EMAIL ADDRESS>\n\
 *\n\
 * @version '+time.strftime("%Y-%m-%d")+'\n\
 * Created on '+time.strftime("%Y-%m-%d")+'.\n\
 */\n'
  return result

def checkName(m, p):
  result = ''
  if( not m.isalpha() ):
    return result
  if( len(m) > 6 ):
    pos = m.find("Module", len(m)-6)
    if( pos != -1 ):
      result = m[:-6]
    else:
      pos = m.find("module", len(m)-6)
      if( pos != -1 ):
        result = m[:-6]
      else:
        pos = m.find("modul", len(m)-6)
        if( pos != -1 ):
          result = m[:-6]
        else:
          pos = m.find("Modul", len(m)-6)
          if( pos != -1 ):
            result = m[:-6]
          else:
            result = m
  else:
    result = m
  if( result != '' ):
    for name in os.listdir(p):
      if( name == result + 'Module' ):
        return ''
  return result

def settingsContent(m, p):
  result = license(p + 'Settings.h') + '\n\
#pragma once\n\n\
namespace smtrat\n\
{\n\
    struct ' + p + 'Settings1\n\
    {\n\
        /**\n\
         * Example for a setting.\n\
         */\n\
        static const bool example_setting = true;\n\
    };\n\
}\n'
  return result

def explicitTemplateDeclarationContent(m, p):
  result = license(m + 'Instantiation.h') + '\n\n\
namespace smtrat\n\
{\n\
    extern template class '+p+'Module<'+p+'Settings@SMTRAT_'+p+'_SETTINGS@>;\n\
}'
  return result

def explicitTemplateDefinitionContent(m, p):
  result = license(m + '.cpp') + '\n\n\
#include "'+p+'Module.h"\n\n\
namespace smtrat\n\
{\n\
    template class '+p+'Module<'+p+'Settings@SMTRAT_'+p+'_SETTINGS@>;\n\
}'
  return result

def statisticsContent(m, p):
  result = license(p + 'Statistics.h') + '\n\n\
#pragma once\n\n\
#include "../../config.h"\n\
#ifdef SMTRAT_DEVOPTION_Statistics\n\
#include "../../utilities/stats/Statistics.h"\n\n\
namespace smtrat\n\
{\n\
    class '+p+'Statistics : public Statistics\n\
    {\n\
    private:\n\
        // Members.\n\
        /**\n\
         * Example for a statistic.\n\
         */\n\
        size_t mExampleStatistic;\n\n\
    public:\n\
        // Override Statistics::collect.\n\
        void collect()\n\
        {\n\
           Statistics::addKeyValuePair( "example_statistic", mExampleStatistic );\n\
        }\n\n\
        void foo()\n\
        {\n\
            ++mExampleStatistic;\n\
        }\n\n\
        '+p+'Statistics( const std::string& _statisticName ): \n\
            Statistics( _statisticName, this ),\n\
            mExampleStatistic( 0 )\n\
        {}\n\n\
        ~'+p+'Statistics() {}\n\
    };\n\
}\n\n\
#endif\n'
  return result
  
def cmakeContent(m, p, s):
  result = ''
  if(s):
    result = 'set(SMTRAT_' + p + '_SETTINGS "1" CACHE STRING "Number of setting used for ' + m + '")'
  result = result + '\n\
BeginDefineModule()\n\
ModuleMainHeader('+m+'/'+m+'.h)\n\
FILE(GLOB_RECURSE sources *.cpp)\n\
foreach(src ${sources})\n\
    AddModuleSource(${src})\n\
endforeach()\n\
ModuleName('+m+')\n'
  if(s):
    result = result + 'ModuleClass('+m+'<'+p+'Settings${SMTRAT_'+p+'_SETTINGS}>'+')\n'
  else:
    result = result + 'ModuleClass('+m+')\n'
  result = result + 'ModuleVersion(0 0 1)\n\
EndDefineModule(moduleEnabled)\n\
\n\
if(${moduleEnabled})\n\
    configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/'+m+'/'+m+'.cpp.in ${CMAKE_SOURCE_DIR}/src/lib/modules/'+m+'/'+m+'.cpp )\n\
    configure_file( ${CMAKE_SOURCE_DIR}/src/lib/modules/'+m+'/'+m+'Instantiation.h.in ${CMAKE_SOURCE_DIR}/src/lib/modules/'+m+'/'+m+'Instantiation.h )\n\
    # do something\n\
endif()'
  return result

def texContent():
  result = "Implements ...\n\n\paragraph{Efficiency} ...\n"
  return result 

def headerContent(m, p, s):
  result = license(m + '.h') + '\n\
#pragma once\n\
\n\
#include "../../solver/Module.h"\n\
#include "'+p+'Statistics.h"\n'
  if(s):
    result = result + '#include "'+p+'Settings.h"'
  result = result + '\n\
namespace smtrat\n\
{\n'
  if(s):
    result = result + '    template<typename Settings>\n'
  result = result + '    class '+m+' : public Module\n\
    {\n\
        private:\n\
            // Members.\n\n\
        public:\n\
            '+m+'( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );\n\
\n\
            ~'+m+'();\n\
\n\
            // Main interfaces.\n\n\
            /**\n\
             * Informs the module about the given constraint. It should be tried to inform this\n\
             * module about any constraint it could receive eventually before assertSubformula\n\
             * is called (preferably for the first time, but at least before adding a formula\n\
             * containing that constraint).\n\
             * @param _constraint The constraint to inform about.\n\
             * @return false, if it can be easily decided whether the given constraint is inconsistent;\n\
             *          true, otherwise.\n\
             */\n\
            bool informCore( const FormulaT& _constraint );\n\n\
            /**\n\
             * Informs all backends about the so far encountered constraints, which have not yet been communicated.\n\
             * This method must not and will not be called more than once and only before the first runBackends call.\n\
             */\n\
	        void init();\n\n\
            /**\n\
             * The module has to take the given sub-formula of the received formula into account.\n\
             *\n\
             * @param _subformula The sub-formula to take additionally into account.\n\
             * @return false, if it can be easily decided that this sub-formula causes a conflict with\n\
             *          the already considered sub-formulas;\n\
             *          true, otherwise.\n\
             */\n\
            bool addCore( ModuleInput::const_iterator _subformula );\n\n\
            /**\n\
             * Removes the subformula of the received formula at the given position to the considered ones of this module.\n\
             * Note that this includes every stored calculation which depended on this subformula, but should keep the other\n\
             * stored calculation, if possible, untouched.\n\
             *\n\
             * @param _subformula The position of the subformula to remove.\n\
             */\n\
            void removeCore( ModuleInput::const_iterator _subformula );\n\n\
            /**\n\
             * Updates the current assignment into the model.\n\
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.\n\
             */\n\
            void updateModel() const;\n\n\
            /**\n\
             * Checks the received formula for consistency.\n\
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.\n\
             * @return True,    if the received formula is satisfiable;\n\
             *         False,   if the received formula is not satisfiable;\n\
             *         Unknown, otherwise.\n\
             */\n\
            Answer checkCore( bool _full );\n\n\
    };\n\
}\n'
  if(s):
    result = result + '\n#include "'+m+'.tpp"\n'
    result = result + '\n#include "'+m+'Instantiation.h"\n'
  return result

def sourceContent(m, s):
  templatePrefix = ''
  if(s):
    templatePrefix = '    template<class Settings>\n'
  templateInst = ''
  if(s):
    templateInst = '<Settings>'
  result = ''
  if(s):
    result = license(m + '.tpp')
  else:
    result = license(m + '.cpp')
  result = result + '\n#include "'+m+'.h"\n\
\n\
namespace smtrat\n\
{\n\
    /**\n\
     * Constructors.\n\
     */\n\
\n'+templatePrefix+'\
    '+m+templateInst+'::'+m+'( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):\n\
        Module( _type, _formula, _conditionals, _manager ) \n\
    {}\n\
\n\
    /**\n\
     * Destructor.\n\
     */\n\
\n'+templatePrefix+'\
    '+m+templateInst+'::~'+m+'()\n\
    {}\n\
\n\
\n'+templatePrefix+'\
    bool '+m+templateInst+'::informCore( const FormulaT& _constraint )\n\
    {\n\
        // Your code.\n\
        return true; // This should be adapted according to your implementation.\n\
    }\n\
\n'+templatePrefix+'\
    void '+m+templateInst+'::init()\n\
    {}\n\
\n'+templatePrefix+'\
    bool '+m+templateInst+'::addCore( ModuleInput::const_iterator _subformula )\n\
    {\n\
        // Your code.\n\
        return true; // This should be adapted according to your implementation.\n\
    }\n\
\n'+templatePrefix+'\
    void '+m+templateInst+'::removeCore( ModuleInput::const_iterator _subformula )\n\
    {\n\
        // Your code.\n\
    }\n\
\n'+templatePrefix+'\
    void '+m+templateInst+'::updateModel() const\n\
    {\n\
        mModel.clear();\n\
        if( solverState() == True )\n\
        {\n\
            // Your code.\n\
        }\n\
    }\n\
\n'+templatePrefix+'\
    Answer '+m+templateInst+'::checkCore( bool _full )\n\
    {\n\
        // Your code.\n\
        return Unknown; // This should be adapted according to your implementation.\n\
    }\n\
}'
  return result



# Print usage information
def printUsage():
  print( "Usage: python [OPTIONS] "+sys.argv[0]+" m\n" )
  print( "            m: name of the module to create (only characters are allowed and")
  print( "               existing module names or the name Module are prohibited);" )
  print( "               if the name does not have the suffix Module, it will be appended" )
  print( "            OPTIONS:" )
  print( "                      -s or --with-settings: creates the module with settings" )
  print( "" )
  print( "Example: python "+sys.argv[0]+" MyModule" )

#
# Parse input.
#
moduleName = ''
moduleNamePref = ''
withSettings = False
modulesPath = 'src/lib/modules/'
i = 0
for entry in sys.argv:
  try: 
    if( i > 0 ):
      if( entry == "-h" or entry == "--help" ):
        printUsage()
        sys.exit(1)
      if( entry == "-s" or entry == "--with-settings"):	
        withSettings = True
      else:
        moduleNamePref = checkName(entry, modulesPath)
        if( moduleNamePref != '' ):
          moduleName = moduleNamePref + 'Module'
        else:
          print( "Error: The given module name is inappropriate." )
          printUsage()
          sys.exit(0)
  except ValueError:
    print( "Error:",entry, "should be an appropriate value at position %i." % i )
    printUsage()
    sys.exit(0)
  i += 1
if i != 2 and i != 3:
  print( "Error: Insufficient number of arguments." )
  printUsage()
  sys.exit(0)
  

moduleDirectory = modulesPath + moduleName
if not os.path.isdir(moduleDirectory):
  os.makedirs(moduleDirectory)

cmakeFile = open(moduleDirectory + '/CMakeLists.txt', 'w')
cmakeFile.write(cmakeContent(moduleName,moduleNamePref,withSettings))
print('Writing ' + moduleDirectory + '/CMakeLists.txt ...')
cmakeFile.close()

headerFile = open(moduleDirectory + '/' + moduleName + '.h', 'w')
print('Writing ' + moduleDirectory + '/' + moduleName + '.h ...')
headerFile.write(headerContent(moduleName,moduleNamePref,withSettings))
headerFile.close()

texFile = open(moduleDirectory + '/' + moduleName + '.tex', 'w')
print('Writing ' + moduleDirectory + '/' + moduleName + '.tex ...')
texFile.write(texContent())
texFile.close()

if(withSettings):
  sourceFile = open(moduleDirectory + '/' + moduleName + '.tpp', 'w')
  print('Writing ' + moduleDirectory + '/' + moduleName + '.tpp ...')
else:
  sourceFile = open(moduleDirectory + '/' + moduleName + '.cpp', 'w')
  print('Writing ' + moduleDirectory + '/' + moduleName + '.cpp ...')
sourceFile.write(sourceContent(moduleName,withSettings))
sourceFile.close()

if(withSettings):
  settingsFile = open(moduleDirectory + '/' + moduleNamePref + 'Settings.h', 'w')
  print('Writing ' + moduleDirectory + '/' + moduleNamePref + 'Settings.h ...')
  settingsFile.write(settingsContent(moduleName,moduleNamePref))
  settingsFile.close()
  expTempDecl = open(moduleDirectory + '/' + moduleName + 'Instantiation.h.in', 'w')
  print('Writing ' + moduleDirectory + '/' + moduleName + 'Instantiation.h.in ...')
  expTempDecl.write(explicitTemplateDeclarationContent(moduleName,moduleNamePref))
  expTempDecl.close()
  expTempDef = open(moduleDirectory + '/' + moduleName + '.cpp.in', 'w')
  print('Writing ' + moduleDirectory + '/' + moduleName + '.cpp.in ...')
  expTempDef.write(explicitTemplateDefinitionContent(moduleName,moduleNamePref))
  expTempDef.close()
  
statisticsFile = open(moduleDirectory + '/' + moduleNamePref + 'Statistics.h', 'w')
print('Writing ' + moduleDirectory + '/' + moduleNamePref + 'Statistics.h ...')
statisticsFile.write(statisticsContent(moduleName,moduleNamePref))
statisticsFile.close()

print('\nPlease remove the File CMakeCache.txt in your build directory and set the compiler flag SMTRAT_ENABLE_' + moduleNamePref + 'Module to ON (for instance by the use of ccmake ..)')

sys.exit(1)

