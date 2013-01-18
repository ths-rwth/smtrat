/* 
 * File:   AddModules.h
 * Author: Sebastian Junges
 *
 * Created on January 12, 2013, 3:39 PM
 */

#pragma once 

#include "../Manager.h"
#include "ModuleType.h"
#include "Modules.h"
#include "../config.h"
#include "../RuntimeSettings.h"

#include <list>
#include <string>

namespace smtrat {
std::list<std::pair<std::string, RuntimeSettings*> > addModules(Manager* manager) {
		typedef std::pair<std::string, RuntimeSettings*> NameAndSettings ;
		// List of settings objects
		std::list<NameAndSettings> settingsObjects;
		//
        // Add all existing modules, as well as the settings
        //
        
		manager->addModuleType( MT_VSModule, new StandardModuleFactory< VSModule >( ) ); 

		manager->addModuleType( MT_CNFerModule, new StandardModuleFactory< CNFerModule >( ) ); 

		manager->addModuleType( MT_CADModule, new StandardModuleFactory< CADModule >( ) ); 

		manager->addModuleType( MT_LRAModule, new StandardModuleFactory< LRAModule >( ) ); 

		manager->addModuleType( MT_SATModule, new StandardModuleFactory< SATModule >( ) ); 

		// Return he list of settings objects, so any method managing them gets them.
		return settingsObjects;
}
}


