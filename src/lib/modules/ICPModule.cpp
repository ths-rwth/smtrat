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
         //TODO: preprocessing
         const ex constr = _constraint->lhs();
         cout << "Constraint: " << endl;
         constr.dbgprint();
         if (isLinear(constr)){
             cout << "is linear." << endl;
         }else{
             cout << "is nonlinear." << endl;
         }
         
         return true; 
     }
     
     bool ICPModule::assertSubformula( Formula::const_iterator _formula){
         Formula* f = *_formula;
         const Constraint* constr = &f->constraint();
         mActiveConstraints[constr] = true;
         
         
         return true;
     }
            
     void ICPModule::removeSubformula( Formula::const_iterator _formula){
         Formula* f = *_formula;
         const Constraint* constr = &f->constraint();
         mActiveConstraints[constr] = false;
     }
     
     Answer ICPModule::isConsistent(){
         //TODO: Intelligent choice of constraints
         ActiveTable::iterator it = mActiveConstraints.begin();
         std::pair<const Constraint*,symbol> tmp = chooseConstraint(it);
         const Constraint* constr = tmp.first;
         symbol variable = tmp.second;
         cout << "Chosen constraint: " << endl;
         constr->lhs().dbgprint();
         
         //fill table if necessary
         if(!mTableau.contains(constr->lhs())){
            GiNaC::symtab::const_iterator it;
            std::pair<GiNaC::ex, GiNaC::symbol> item;
         
            for (it = constr->variables().begin(); it != constr->variables().end(); it++) {
                item.first = constr->lhs();
                item.second = ex_to<symbol > (it->second);
                mTableau.addEntry(item, constr->lhs().diff(item.second));
            }
         }
         
         //Actual compression
         GiNaCRA::Icp icp;
         
         //TODO: Validation of gained interval box
         return Answer();
     }
     
     std::pair<const Constraint*,symbol> ICPModule::chooseConstraint(ActiveTable::iterator _it){
         while (!_it->second){
             _it++;
         }
         std::pair<const Constraint*, symbol> item;
         item.first = _it->first;
         item.second = ex_to<symbol>(_it->first->variables().begin()->second);
         return item;
     }
     
     bool ICPModule::isLinear(const ex& _expr){
         bool isLinear = true;
         std::vector<symbol> variables;
         GiNaCRA::Icp icp;
         icp.searchVariables(_expr,&variables);
         std::vector<symbol>::iterator it;
         
         for(it = variables.begin(); it != variables.end(); it++){
             for(int i = /*_expr.ldegree(*it)*/ 1;i<_expr.degree(*it);i++){
                 cout << "Variable: " << endl;
                 symbol s = *it;
                 s.dbgprint();
                 cout << "Degree: " << i << endl;
                 cout << "Coefficient: " << _expr.coeff(*it,i) << endl;
                 isLinear = !is_a<numeric>(_expr.coeff(*it,i)) ? false : true;
             }
         }
         
         return isLinear;
     }
}