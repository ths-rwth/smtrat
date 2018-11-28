#!/usr/bin/python

import sys
import os
import time
import re

def license(filename):
	result = """/**
 * @file """ + filename + """
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version """ + time.strftime("%Y-%m-%d") + """
 * Created on """ + time.strftime("%Y-%m-%d") + """.
 */
"""
	return result

def checkName(module, basePath):
	namere = "^([a-zA-Z]+?)(Module?)?$"
	match = re.match(namere, module)
	if match == None:
		print("The module name should only contain characters. ([a-zA-Z]+)")
		return None
	module = match.group(1)
	if os.path.isdir(basePath + module + "Module"):
		print("The module \"" + module + "Module\" already exists.")
		return None
	print("The module name will be \"" + module + "Module\".")
	return module

def replacePlaceholder(str, module):
	return str.replace("<MODULENAME>", module).replace("<CLASSNAME>", module + "Module")

def cmakeContent(module):
	result = """
BeginDefineModule()
ModuleMainHeader(<CLASSNAME>/<CLASSNAME>.h)
ModuleName(<CLASSNAME>)
ModuleVersion(0 0 1)
EndDefineModule()
"""
	return replacePlaceholder(result, module)


def texContent(module):
	result = "Implements ...\n\n\paragraph{Efficiency} ...\n"
	return result 

def headerContent(module):
	result = license(module + 'Module.h') + """
#pragma once

#include "../../solver/Module.h"
#include \"<MODULENAME>Statistics.h\"
#include \"<MODULENAME>Settings.h\"

namespace smtrat
{
	template<typename Settings>
	class <CLASSNAME> : public Module
	{
		private:
#ifdef SMTRAT_DEVOPTION_Statistics
			<MODULENAME>Statistics mStatistics;
#endif
			// Members.
			
		public:
			typedef Settings SettingsType;
			std::string moduleName() const {
				return SettingsType::moduleName;
			}
			<CLASSNAME>(const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = nullptr);

			~<CLASSNAME>();
			
			// Main interfaces.
			/**
			 * Informs the module about the given constraint. It should be tried to inform this
			 * module about any constraint it could receive eventually before assertSubformula
			 * is called (preferably for the first time, but at least before adding a formula
			 * containing that constraint).
			 * @param _constraint The constraint to inform about.
			 * @return false, if it can be easily decided whether the given constraint is inconsistent;
			 *		  true, otherwise.
			 */
			bool informCore( const FormulaT& _constraint );

			/**
			 * Informs all backends about the so far encountered constraints, which have not yet been communicated.
			 * This method must not and will not be called more than once and only before the first runBackends call.
			 */
			void init();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Updates the current assignment into the model.
			 * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
			 */
			void updateModel() const;

			/**
			 * Checks the received formula for consistency.
			 * @return True,	if the received formula is satisfiable;
			 *		 False,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
}
"""
	return replacePlaceholder(result, module)

def sourceContent(module):
	result = license(module + '.cpp') + """
#include "<CLASSNAME>.h"

namespace smtrat
{
	template<class Settings>
	<CLASSNAME><Settings>::<CLASSNAME>(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
		Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
		, mStatistics(Settings::moduleName)
#endif
	{}
	
	template<class Settings>
	<CLASSNAME><Settings>::~<CLASSNAME>()
	{}
	
	template<class Settings>
	bool <CLASSNAME><Settings>::informCore( const FormulaT& _constraint )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void <CLASSNAME><Settings>::init()
	{}
	
	template<class Settings>
	bool <CLASSNAME><Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void <CLASSNAME><Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void <CLASSNAME><Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer <CLASSNAME><Settings>::checkCore()
	{
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
"""
	return replacePlaceholder(result, module)

def settingsContent(module):
  result = license(module + 'Settings.h') + """
#pragma once

namespace smtrat
{
	struct <MODULENAME>Settings1
	{
		/// Name of the Module
		static constexpr auto moduleName = \"<CLASSNAME><<MODULENAME>Settings1>\";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
"""
  return replacePlaceholder(result, module)

def statisticsContent(module):
	result = license(module + 'Statistics.h') + """
#pragma once

#ifdef SMTRAT_DEVOPTION_Statistics
#include "../../utilities/stats/Statistics.h"

namespace smtrat
{
	class <MODULENAME>Statistics : public Statistics
	{
	private:
		// Members.
		/**
		 * Example for a statistic.
		 */
		size_t mExampleStatistic;
	public:
		// Override Statistics::collect.
		void collect()
		{
		   Statistics::addKeyValuePair( "example_statistic", mExampleStatistic );
		}
		void foo()
		{
			++mExampleStatistic;
		}
		<MODULENAME>Statistics( const std::string& _statisticName ):
			Statistics( _statisticName, this ),
			mExampleStatistic( 0 )
		{}
		~<MODULENAME>Statistics() {}
	};
}

#endif
"""
	return replacePlaceholder(result, module)

def instantiationContent(module):
  result = license(module + 'Instantiation.h.in') + """
#include "${Prefix}Module.h"

namespace smtrat {
${INSTANTIATIONS}
}
"""
  return replacePlaceholder(result, module)

# Print usage information
def printUsage():
	print( "Usage: python " + sys.argv[0] + " m\n" )
	print( "			m: name of the module to create (only characters are allowed and")
	print( "			   existing module names or the name Module are prohibited);" )
	print( "			   if the name does not have the suffix Module, it will be appended" )
	print( "" )
	print( "Example: python " + sys.argv[0] + " MyModule" )

#
# Parse input.
#
moduleName = None
modulesPath = 'src/lib/modules/'
for entry in sys.argv[1:]:
	if entry in ["-h", "--help"]:
		printUsage()
		sys.exit(0)
	moduleName = checkName(entry, modulesPath)
	if moduleName == None:
		sys.exit(1)
if moduleName == None:
	print("No argument was given.")
	printUsage()
	sys.exit(1)

moduleDirectory = modulesPath + moduleName + "Module/"
if not os.path.isdir(moduleDirectory):
	os.makedirs(moduleDirectory)

files = {
	"CMakeLists.txt" : cmakeContent,
	moduleName + "Module.h": headerContent,
	moduleName + "Module.cpp": sourceContent,
	moduleName + "Module.tex": texContent,
	moduleName + "Settings.h": settingsContent,
	moduleName + "Statistics.h": statisticsContent,
	"Instantiation.h.in": instantiationContent,
}

for file in files:
	f = files[file]
	fd = open(moduleDirectory + file, 'w')
	print('Writing ' + moduleDirectory + file + ' ...')
	fd.write(f(moduleName))
	fd.close()

print('\nPlease remove the File CMakeCache.txt in your build directory!')
