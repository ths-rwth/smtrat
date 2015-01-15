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
/**
 * @file ModuleInput.h
 * @author Florian Corzilius
 * @version 2014-05-16
 */

#pragma once


#include <algorithm>
#include <list>
#include <vector>
#include <set>
#include <iterator>
#include "../Common.h"
#include "../datastructures/Assignment.h"
#include "../../cli/parser/ParserTypes.h"
#include "../config.h"

#define MODULE_INPUT_USE_HASHING_FOR_FIND

namespace smtrat
{
    
    /// Stores a formula along with its origins.
    class FormulaWithOrigins
    {
        // Member
        
        /// The formula.
        FormulaT mFormula;
        /// The formulas origins.
        std::vector<FormulasT> mOrigins;
        /// The deduction flag, which indicates, that this formula g is a direct sub-formula of
        /// a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
        mutable bool mDeducted;
        
    public:
        
        FormulaWithOrigins(); // Default constructor disabled.
        
        /**
         * Constructs a formula with empty origins.
         * @param _formula The formula of the formula with origins to construct.
         */
        FormulaWithOrigins( const FormulaT& _formula ):
            mFormula( _formula ),
            mOrigins(),
            mDeducted( false )
        {}
        
        /**
         * Constructs a formula with the given origins.
         * @param _formula The formula of the formula with origins to construct.
         * @param _origins The origins of the formula with origins to construct.
         */
        FormulaWithOrigins( const FormulaT& _formula, const std::vector<FormulasT>& _origins ):
            mFormula( _formula ),
            mOrigins( _origins ),
            mDeducted( false )
        {}
        
        /**
         * Constructs a formula with the given origins.
         * @param _formula The formula of the formula with origins to construct.
         * @param _origins The origins of the formula with origins to construct.
         */
        FormulaWithOrigins( const FormulaT& _formula, std::vector<FormulasT>&& _origins ):
            mFormula( _formula ),
            mOrigins( std::move( _origins ) ),
            mDeducted( false )
        {}
        
        FormulaWithOrigins( const FormulaWithOrigins& ); // Copy constructor disabled.
        
        /**
         * @param _fwoA The first formula with origins to compare.
         * @param _fwoB The second formula with origins to compare.
         * @return true, if the formula of the first formula with origins is less than the formula of the second formula with origins;
         *         false, otherwise.
         */
        friend bool operator<( const FormulaWithOrigins& _fwoA, const FormulaWithOrigins& _fwoB )
        {
            return _fwoA.formula() < _fwoB.formula();
        }
        
        /**
         * @param _fwoA The first formula with origins to compare.
         * @param _fwoB The second formula with origins to compare.
         * @return true, if the formula of the first formula with origins and the formula of the second formula with origins are equal;
         *         false, otherwise.
         */
        friend bool operator==( const FormulaWithOrigins& _fwoA, const FormulaWithOrigins& _fwoB )
        {
            return _fwoA.formula() == _fwoB.formula();
        }
        
        /**
         * @return A constant reference to the formula.
         */
        const FormulaT& formula() const
        {
            return mFormula;
        }
        
        /**
         * @return A constant reference to the origins.
         */
        const std::vector<FormulasT>& origins() const
        {
            return mOrigins;
        }
        
        /**
         * @return A reference to the origins.
         */
        std::vector<FormulasT>& rOrigins()
        {
            return mOrigins;
        }

        /**
         * Sets the deduction flag to the given value.
         * @param _deducted The value to set the deduction flag to.
         */
        void setDeducted( bool _deducted ) const
        {
            mDeducted = _deducted;
        }

        /**
         * @return The deduction flag, which indicates, that this formula g is a direct sub-formula of
         *          a conjunction of formulas (and g f_1 .. f_n), and, that (implies (and f_1 .. f_n) g) holds.
         */
        bool deducted() const
        {
            return mDeducted;
        }
    };
    
    class Manager; // Forward declaration.
    
    class Module; // Forward declaration.
    
    /**
     * The input formula a module has to consider for it's satisfiability check. It is a list of formulas
     * and semantically considered as their conjunction.
     */
    class ModuleInput : private std::list<FormulaWithOrigins>
    {
        friend class Module;
        
        friend class Manager;
        
    private:
        
        typedef std::list<FormulaWithOrigins> super;
        
        
    public:
            
        /// Passing through the list::iterator.
        typedef super::iterator iterator;
        /// Passing through the list::const_iterator.
        typedef super::const_iterator const_iterator;
        
    private:
        
        // Member.
        /// Store some properties about the conjunction of the stored formulas.
        mutable carl::Condition mProperties;
        #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
        carl::FastMap<FormulaT,iterator> mFormulaPositionMap;
        #endif

    public:
            
        /**
         * Constructs a module input.
         */
        ModuleInput(): 
            std::list<FormulaWithOrigins>(),
            mProperties()
            #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
            ,
            mFormulaPositionMap()
            #endif
        {}
        
        // Methods.
        
        /**
         * @return All known properties of the underlying formula of this module input.
         */
        const carl::Condition& properties() const
        {
            updateProperties();
            return mProperties;
        }
        
        /**
         * @return true, if this formula is a conjunction of constraints;
         *         false, otherwise.
         */
        bool isConstraintConjunction() const
        {
            if( carl::PROP_IS_PURE_CONJUNCTION <= mProperties )
                return !(carl::PROP_CONTAINS_BOOLEAN <= mProperties) && !(carl::PROP_CONTAINS_UNINTERPRETED_EQUATIONS <= mProperties);
            else
                return false;
        }

        /**
         * @return true, if this formula is a conjunction of real constraints;
         *         false, otherwise.
         */
        bool isRealConstraintConjunction() const
        {
            return isConstraintConjunction() && !(carl::PROP_CONTAINS_INTEGER_VALUED_VARS <= mProperties);
        }

        /**
         * @return true, if this formula is a conjunction of integer constraints;
         *         false, otherwise.
         */
        bool isIntegerConstraintConjunction() const
        {
            return isConstraintConjunction() && !(carl::PROP_CONTAINS_REAL_VALUED_VARS <= mProperties);
        }
        
        /**
         * @param _assignment The model to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given model;
         *         0, if the given model conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given model conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const Model& _assignment ) const;
        
        /**
         * @param _assignment The assignment to check conjunction of the stored formulas against.
         * @return 1, if the conjunction of the stored formulas is satisfied by the given assignment;
         *         0, if the given assignment conflicts the conjunction of the stored formulas;
         *         2, if it cannot be determined cheaply, whether the given assignment conflicts or satisfies 
         *            the conjunction of the stored formulas.
         */
        unsigned satisfiedBy( const EvalRationalMap& _assignment ) const;
        
        iterator begin()
        {
            return super::begin();
        }
        
        iterator end()
        {
            return super::end();
        }
        
        const_iterator begin() const
        {
            return super::begin();
        }
        
        const_iterator end() const
        {
            return super::end();
        }
        
        bool empty() const
        {
            return super::empty();
        }
        
        size_t size() const
        {
            return super::size();
        }
        
        iterator find( const FormulaT& _formula );
        
        const_iterator find( const FormulaT& _formula ) const;
        
        iterator find( const_iterator _hint, const FormulaT& _formula );
        
        const_iterator find( const_iterator _hint, const FormulaT& _formula ) const;
        
        /**
         * @param _subformula The formula for which to check whether it is one of the stored formulas.
         * @return true, if the given formula is one of the stored formulas;
         *         false, otherwise.
         */
        bool contains( const FormulaT& _subformula ) const
        {
            #ifdef MODULE_INPUT_USE_HASHING_FOR_FIND
            return mFormulaPositionMap.find( _subformula ) != mFormulaPositionMap.end();
            #else
            return std::find( begin(), end(), _subformula ) != end();
            #endif
        }
        
        /**
         * Updates all properties of the formula underlying this module input.
         */
        void updateProperties() const;
        
        /**
         * Collects all real valued variables occurring in this formula.
         * @param _realVars The container to collect the real valued variables in.
         */
        void realValuedVars( carl::Variables& _realVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().realValuedVars( _realVars );
        }

        /**
         * Collects all integer valued variables occurring in this formula.
         * @param _intVars The container to collect the integer valued variables in.
         */
        void integerValuedVars( carl::Variables& _intVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().integerValuedVars( _intVars );
        }

        /**
         * Collects all arithmetic variables occurring in this formula.
         * @param _arithmeticVars The container to collect the arithmetic variables in.
         */
        void arithmeticVars( carl::Variables& _arithmeticVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().arithmeticVars( _arithmeticVars );
        }

        /**
         * Collects all Boolean variables occurring in this formula.
         * @param _booleanVars The container to collect the Boolean variables in.
         */
        void booleanVars( carl::Variables& _booleanVars ) const
        {
            for( const FormulaWithOrigins& fwo : *this )
                fwo.formula().booleanVars( _booleanVars );
        }
        
        struct IteratorCompare
        {
            bool operator() ( const_iterator i1, const_iterator i2 ) const
            {
                return (*i1) < (*i2);
            }
        };
        
        /**
         * @return The string representation of this module input.
         */
        std::string toString() const
        {
            std::string result = "(and";
            for( auto& fwo : *this )
                result += " " + fwo.formula().toString();
            result += ")";
            return result;
        }
        
        explicit operator FormulaT() const
        {
            FormulasT subFormulas;
            for( auto& fwo : *this )
                subFormulas.insert( fwo.formula() );
            return FormulaT( carl::FormulaType::AND, subFormulas );
        }
        
//        friend std::ostream& operator<<( std::ostream& _out, const ModuleInput& _mi )
//        {
//            return _out << _mi.toString()
//        }
        
        iterator erase( iterator _formula );
        
        bool removeOrigin( iterator _formula, const FormulaT& _origin );
        
        bool removeOrigins( iterator _formula, const std::vector<FormulasT>& _origins );
        
        bool removeOrigins( iterator _formula, const FormulasT& _origins );
        
        std::pair<iterator,bool> add( const FormulaT& _formula )
        {
            FormulasT origins;
            return add( _formula, std::move( origins ) );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, const FormulaT& _origin )
        {
            FormulasT origins;
            origins.insert( _origin );
            return add( _formula, std::move( origins ) );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, const FormulasT& _origins )
        {
            FormulasT originsCopy( _origins );
            return add( _formula, std::move( originsCopy ) );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, const std::vector<FormulasT>& _origins )
        {
            std::vector<FormulasT> originsCopy( _origins );
            return add( _formula, std::move( originsCopy ) );
        }
        
        std::pair<iterator,bool> add( const FormulaT& _formula, FormulasT&& _origins );
        
        std::pair<iterator,bool> add( const FormulaT& _formula, std::vector<FormulasT>&& _origins );
    };
    
    void annotateFormula( const FormulaT&, const std::vector<parser::Attribute>& );
}    // namespace smtrat
