/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

/* 
 * @file   ICPModule.h
 * @author name surname <emailadress>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#ifndef ICPMODULE_H
#define	ICPMODULE_H

#include "../Module.h"

namespace smtrat
{
    class ICPModule:
        public Module
    {
        public:
            // Interfaces.
            bool inform( const Constraint* const );
            bool assertSubformula( Formula::const_iterator );
            void removeSubformula( Formula::const_iterator );
            Answer isConsistent();
    };
}//namespace smtrat

#endif	/* ICPMODULE_H */

