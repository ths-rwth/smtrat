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

namespace smtrat {
void addModules(Manager* manager) {
        /*
         * Add all existing modules.
         */
         manager->addModuleType( MT_GroebnerModule, new StandardModuleFactory< GroebnerModule<GBSettings> >( ) ); 
 manager->addModuleType( MT_CNFerModule, new StandardModuleFactory< CNFerModule >( ) ); 

}
}


