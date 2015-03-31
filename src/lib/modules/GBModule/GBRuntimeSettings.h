/* 
 * File:   GBRuntimeSettings.h
 * Author: Sebastian Junges
 *
 * Created on January 13, 2013, 4:25 PM
 */

#pragma once 

namespace smtrat 
{
class GBRuntimeSettings : public RuntimeSettings 
{
public:
    GBRuntimeSettings(const std::string& name) : RuntimeSettings(name) {}
    ~GBRuntimeSettings() {}
};
}

