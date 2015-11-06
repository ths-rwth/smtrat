/**
 * @file ModuleSettings.h
 * @author Florian Corzilius
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once
#include <iostream>

namespace smtrat
{
    struct ModuleSettings
    {
        static constexpr auto moduleName = "Module";
        
        friend std::ostream& operator<<( std::ostream& _os, const ModuleSettings& _settings )
        {
            _os << _settings.moduleName;
            return _os;
        }
    };
}
