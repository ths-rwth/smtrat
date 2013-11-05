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
 * @file   DerivativeTable.h
 * @author stefan schupp
 *
 * Created on October 16, 2012, 1:22 PM
 */

#ifndef DERIVATIVETABLE_H
#define	DERIVATIVETABLE_H

#include <tuple>

namespace smtrat
{
//    class DerivativeTable{
//        public:
//            /**
//             * Typedefs:
//             */
//            typedef std::map<std::pair<GiNaC::ex,GiNaC::symbol>, GiNaC::ex > Table;
//    
//        private:
//            /**
//             * Members:
//             */
//            Table mTable;
//             
//        public:
//            /**
//             * Constructors:
//             */
//            DerivativeTable(){
//                mTable = Table();
//            }
//            
//            /**
//            * Destructor:
//            */
//            ~DerivativeTable(){};
//            
//            /**
//             * Functions:
//             */
//            void addEntry(const std::pair<GiNaC::ex,GiNaC::symbol>& _key, const GiNaC::ex& _value){
//                mTable[_key] = _value;
//            }
//            
//            GiNaC::ex getEntry(const std::pair<GiNaC::ex,GiNaC::symbol>& _key){
//                return mTable[_key];
//            }
//            
//            bool contains(const GiNaC::ex& _constraint){
//                bool contains = false;
//                Table::iterator it;
//                for(it = mTable.begin(); it != mTable.end();it++){
//                    if (it->first.first == _constraint.lhs()){
//                        contains = true;
//                    }
//                }
//                return contains;
//            }
//            
//        private:
//            /**
//             * Methods:
//             */
//    };
}

#endif	/* DERIVATIVETABLE_H */

