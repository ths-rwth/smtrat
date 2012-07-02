/*
 * Bound.cpp
 *
 *  Created on: Apr 30, 2012
 *      Author: cornflake
 */

#include "Bound.h"

namespace smtrat
{
    Bound::~Bound(){}

    Real Bound::getBound()
    {
        return this->bound;
    }

    void Bound::setBound( Real bound )
    {
        this->bound = bound;
    }

    void Bound::activate()
    {
        this->activated = true;
    }

    void Bound::deactivate()
    {
        this->activated = false;
    }

    bool Bound::isActive()
    {
        return this->activated;
    }

}
