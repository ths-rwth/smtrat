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
 * @file   ICPModule.cpp
 * @author name surname <emailadress>
 *
 * Created on October 16, 2012, 1:07 PM
 */

#include "ICPModule.h"

using namespace GiNaC;
using namespace std;

namespace smtrat{
    /**
     * Constructor
     */
    ICPModule::ICPModule( Manager* const _tsManager, const Formula* const _formula ):
        Module( _tsManager, _formula )
    {
        this->mModuleType = MT_ICPModule;
    }
    /**
     * Destructor:
     */
    ICPModule::~ICPModule(){}
    
     bool ICPModule::inform( const Constraint* const _constraint){
         GiNaC::ex constr = GiNaC::ex(_constraint->lhs());
         GiNaC::symtab::const_iterator it;
         std::pair<GiNaC::ex, GiNaC::symbol> item;
         for (it = _constraint->variables().begin(); it != _constraint->variables().end(); it++) {
            item.first = constr;
            item.second = ex_to<symbol > (it->second);
            mTableau.addEntry(item, constr.diff(item.second));
            cout << "Constraint: " << endl;
            constr.dbgprint();
            cout << "Symbol: " << endl;
            it->second.dbgprint();
            cout << "Derivative: " << endl;
            constr.diff(item.second).dbgprint(); 
            
         }
         return true; 
     }
     
     bool ICPModule::assertSubformula( Formula::const_iterator ){
         return true;
     }
            
     void ICPModule::removeSubformula( Formula::const_iterator ){
         
     }
     
     Answer ICPModule::isConsistent(){
         return Answer();
     }
}