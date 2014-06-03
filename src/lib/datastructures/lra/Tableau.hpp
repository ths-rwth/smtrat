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
 * @file Tableau.hpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef LRA_TABLEAU_H
#define LRA_TABLEAU_H

#include <vector>
#include <stack>
#include <map>
#include <deque>
#include "Variable.hpp"

//#define LRA_PRINT_STATS

#define LRA_USE_PIVOTING_STRATEGY
#define LRA_REFINEMENT
//#define LRA_EQUATION_FIRST
//#define LRA_LOCAL_CONFLICT_DIRECTED
//#define LRA_USE_ACTIVITY_STRATEGY
#define LRA_USE_THETA_STRATEGY
#ifdef LRA_REFINEMENT
//#define LRA_INTRODUCE_NEW_CONSTRAINTS
#endif
//#define LRA_GOMORY_CUTS
#ifndef LRA_GOMORY_CUTS
//#define LRA_CUTS_FROM_PROOFS
#ifdef LRA_CUTS_FROM_PROOFS
//#define LRA_DEBUG_CUTS_FROM_PROOFS
#endif
#endif

namespace smtrat
{
    namespace lra
    {
        template<typename T1, typename T2>
        class TableauEntry
        {
            private:
                EntryID mUp;
                EntryID mDown;
                EntryID mLeft;
                EntryID mRight;
                Variable<T1, T2>* mRowVar;
                Variable<T1, T2>* mColumnVar;
                T2 mpContent;

            public:
                TableauEntry():
                    mUp( LAST_ENTRY_ID ),
                    mDown( LAST_ENTRY_ID ),
                    mLeft( LAST_ENTRY_ID ),
                    mRight( LAST_ENTRY_ID ),
                    mRowVar( NULL ),
                    mColumnVar( NULL ),
                    mpContent()
                {}
                ;
                TableauEntry( EntryID _up,
                              EntryID _down,
                              EntryID _left,
                              EntryID _right,
                              Variable<T1, T2>* _rowVar,
                              Variable<T1, T2>* _columnVar,
                              const T2& _content ):
                    mUp( _up ),
                    mDown( _down ),
                    mLeft( _left ),
                    mRight( _right ),
                    mRowVar( _rowVar ),
                    mColumnVar( _columnVar ),
                    mpContent( _content )
                {}
                ;
                TableauEntry( const TableauEntry& _entry ):
                    mUp( _entry.mUp ),
                    mDown( _entry.mDown ),
                    mLeft( _entry.mLeft ),
                    mRight( _entry.mRight ),
                    mRowVar( _entry.mRowVar ),
                    mColumnVar( _entry.mColumnVar ),
                    mpContent( _entry.mpContent )
                {}
                ;
                ~TableauEntry()
                {}
                ;
                
                void setVNext( bool downwards, const EntryID _entryId )
                {
                    if( downwards )
                        mDown = _entryId;
                    else
                        mUp = _entryId;
                }
                
                void setHNext( bool leftwards, const EntryID _entryId )
                {
                    if( leftwards )
                        mLeft = _entryId;
                    else
                        mRight = _entryId;
                }
                
                EntryID vNext( bool downwards )
                {
                    if( downwards )
                        return mDown;
                    else
                        return mUp;
                }
                
                EntryID hNext( bool leftwards )
                {
                    if( leftwards )
                        return mLeft;
                    else
                        return mRight;
                }

                Variable<T1, T2>* rowVar() const
                {
                    return mRowVar;
                }

                void setRowVar( Variable<T1, T2>* _rowVar )
                {
                    mRowVar = _rowVar;
                }

                Variable<T1, T2>* columnVar() const
                {
                    return mColumnVar;
                }

                void setColumnVar( Variable<T1, T2>* _columnVar )
                {
                    mColumnVar = _columnVar;
                }

                const T2& content() const
                {
                    return mpContent;
                }

                T2& rContent()
                {
                    return mpContent;
                }
        };

        template <typename T1, typename T2>
        class Tableau
        {
            public:
                struct LearnedBound
                {
                    const Bound<T1, T2>*               newBound;
                    const Bound<T1, T2>*               nextWeakerBound;
                    std::vector< const Bound<T1, T2>*> premise;
                };
            private:
                bool                            mRowsCompressed;
                size_t                          mWidth;
                size_t                          mPivotingSteps;
                #ifdef LRA_USE_PIVOTING_STRATEGY
                size_t                          mMaxPivotsWithoutBlandsRule;
                #endif
                std::list<const smtrat::Formula*>::iterator mDefaultBoundPosition;
                std::stack<EntryID>             mUnusedIDs;
                std::vector<Variable<T1,T2>*>   mRows;       // First element is the head of the row and the second the length of the row.
                std::vector<Variable<T1,T2>*>   mColumns;    // First element is the end of the column and the second the length of the column.
                std::list<std::list<std::pair<Variable<T1,T2>*,T2>>> mNonActiveBasics;
                std::vector<TableauEntry<T1,T2> >* mpEntries;
                std::vector<Variable<T1,T2>*>   mConflictingRows;
                Value<T1>*                      mpTheta;
                std::map< carl::Variable, Variable<T1,T2>*>  mOriginalVars;
                FastPointerMap<Polynomial, Variable<T1,T2>*> mSlackVars;
                FastPointerMap<Constraint, std::vector<const Bound<T1, T2>*>*> mConstraintToBound;
                #ifdef LRA_REFINEMENT
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedLowerBounds;
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedUpperBounds;
                std::vector<typename std::map<Variable<T1,T2>*, LearnedBound>::iterator> mNewLearnedBounds;
                #endif

                class Iterator
                {
                    private:
                        EntryID                            mEntryID;
                        std::vector<TableauEntry<T1,T2> >* mpEntries;

                    public:
                        Iterator( EntryID _start, std::vector<TableauEntry<T1,T2> >* const _entries ):
                            mEntryID( _start ),
                            mpEntries( _entries )
                        {}
                        ;
                        Iterator( const Iterator& _iter ):
                            mEntryID( _iter.entryID() ),
                            mpEntries( _iter.pEntries() )
                        {}
                        ;

                        EntryID entryID() const
                        {
                            return mEntryID;
                        }

                        TableauEntry<T1,T2>& operator *()
                        {
                            return (*mpEntries)[mEntryID];
                        }
                        
                        bool vEnd( bool downwards ) const
                        {
                            return (*mpEntries)[mEntryID].vNext( downwards ) == LAST_ENTRY_ID;
                        }
                        
                        bool hEnd( bool leftwards ) const
                        {
                            return (*mpEntries)[mEntryID].hNext( leftwards ) == LAST_ENTRY_ID;
                        }

                        void vMove( bool downwards )
                        {
                            assert( !vEnd( downwards ) );
                            mEntryID = (*mpEntries)[mEntryID].vNext( downwards );
                        }

                        void hMove( bool leftwards )
                        {
                            assert( !hEnd( leftwards ) );
                            mEntryID = (*mpEntries)[mEntryID].hNext( leftwards );
                        }

                        std::vector<TableauEntry<T1,T2> >* pEntries() const
                        {
                            return mpEntries;
                        }

                        bool operator ==( const Iterator& _iter ) const
                        {
                            return mEntryID == _iter.entryID();
                        }

                        bool operator !=( const Iterator& _iter ) const
                        {
                            return mEntryID != _iter.entryID();
                        }
                };    /* class Tableau<T1,T2>::Iterator */

            public:
                Tableau( std::list<const smtrat::Formula*>::iterator );
                ~Tableau();

                void setSize( size_t _expectedHeight, size_t _expectedWidth, size_t _expectedNumberOfBounds )
                {
                    mRows.reserve( _expectedHeight );
                    mColumns.reserve( _expectedWidth );
                    mpEntries->reserve( _expectedHeight*_expectedWidth+1 );
                    carl::reserve<T1>( 2*(_expectedNumberOfBounds+1) );
                    carl::reserve<T2>( _expectedHeight*_expectedWidth+1 );
                }
                
                size_t size() const
                {
                    return mpEntries->size();
                }

                #ifdef LRA_USE_PIVOTING_STRATEGY
                void setBlandsRuleStart( size_t _start )
                {
                    mMaxPivotsWithoutBlandsRule = _start;
                }
                #endif

                const std::vector<Variable<T1, T2>*>& rows() const
                {
                    return mRows;
                }

                const std::vector<Variable<T1, T2>*>& columns() const
                {
                    return mColumns;
                }
                
                const std::map< carl::Variable, Variable<T1,T2>*>& originalVars() const
                {
                    return mOriginalVars;
                }
                
                const FastPointerMap<Polynomial, Variable<T1,T2>*>& slackVars() const 
                {
                    return mSlackVars;
                }
                
                const FastPointerMap<Constraint, std::vector<const Bound<T1, T2>*>*>& constraintToBound() const
                {
                    return mConstraintToBound;
                }
                
                FastPointerMap<Constraint, std::vector<const Bound<T1, T2>*>*>& rConstraintToBound()
                {
                    return mConstraintToBound;
                }

                size_t numberOfPivotingSteps() const
                {
                    return mPivotingSteps;
                }
                
                void resetNumberOfPivotingSteps() 
                {
                    mPivotingSteps = 0;
                }

                #ifdef LRA_REFINEMENT
                std::map<Variable<T1, T2>*, LearnedBound>& rLearnedLowerBounds()
                {
                    return mLearnedLowerBounds;
                }

                std::map<Variable<T1, T2>*, LearnedBound>& rLearnedUpperBounds()
                {
                    return mLearnedUpperBounds;
                }
                
                std::vector<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator>& rNewLearnedBounds()
                {
                    return mNewLearnedBounds;
                }
                #endif

                smtrat::Formula::const_iterator defaultBoundPosition() const
                {
                    return mDefaultBoundPosition;
                }

                EntryID newTableauEntry( const T2& );
                void removeEntry( EntryID );
                std::pair<const Bound<T1,T2>*, bool> newBound( const smtrat::Constraint* );
                void activateBound( const Bound<T1,T2>*, const PointerSet<Formula>& );
                Variable<T1, T2>* newNonbasicVariable( const smtrat::Polynomial* );
                Variable<T1, T2>* newBasicVariable( const smtrat::Polynomial*, std::map<carl::Variable, Variable<T1, T2>*>& );
                void activateBasicVar( Variable<T1, T2>* );
                void deactivateBasicVar( Variable<T1, T2>* );
                void compressRows();
                void activateBound( const Bound<T1, T2>* );
                void deactivateBound( const Bound<T1, T2>* );
                std::pair<EntryID, bool> nextPivotingElement();
                std::pair<EntryID, bool> isSuitable( const Variable<T1, T2>&, bool ) const;
                bool betterEntry( EntryID, EntryID ) const;
                std::vector< const Bound<T1, T2>* > getConflict( EntryID ) const;
                std::vector< std::set< const Bound<T1, T2>* > > getConflictsFrom( EntryID ) const;
                void updateBasicAssignments( size_t, const Value<T1>& );
                void pivot( EntryID );
                void update( bool downwards, EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
                void addToEntry( const T2&, Iterator&, bool, Iterator&, bool );
                #ifdef LRA_REFINEMENT
                void rowRefinement( Variable<T1, T2>* );
                #endif
                size_t boundedVariables( const Variable<T1,T2>&, size_t = 0 ) const;
                size_t unboundedVariables( const Variable<T1,T2>&, size_t = 0 ) const;
                size_t checkCorrectness() const;
                bool rowCorrect( size_t _rowNumber ) const;
                #ifdef LRA_CUTS_FROM_PROOFS
                const smtrat::Constraint* isDefining( size_t, T2& ) const;
                bool isDefining_Easy( std::vector<size_t>&, size_t );
                bool isDiagonal( size_t, std::vector<size_t>& );
                size_t position_DC( size_t, std::vector<size_t>& );
                size_t revert_diagonals( size_t, std::vector<size_t>& );
                void invertColumn( size_t );
                void addColumns( size_t, size_t, T2 );
                void multiplyRow( size_t, T2 );
                std::pair< const Variable<T1,T2>*, T2 > Scalar_Product( Tableau<T1,T2>&, Tableau<T1,T2>&, size_t, size_t, std::vector<size_t>&, std::vector<size_t>&);
                void calculate_hermite_normalform( std::vector<size_t>& );
                void invert_HNF_Matrix( std::vector<size_t>& );
                smtrat::Polynomial* create_cut_from_proof( Tableau<T1,T2>&, Tableau<T1,T2>&, size_t, std::vector<size_t>&, std::vector<size_t>&, T2&, T2&);
                #endif
                #ifdef LRA_GOMORY_CUTS
                const smtrat::Constraint* gomoryCut( const T2&, Variable<T1, T2>*, std::vector<const smtrat::Constraint*>&);
                #endif
                size_t getNumberOfEntries( Variable<T1,T2>* );
                void collect_premises( Variable<T1,T2>*, PointerSet<Formula>&  );
                void printHeap( std::ostream& = std::cout, int = 30, const std::string = "" ) const;
                void printEntry( EntryID, std::ostream& = std::cout, int = 20 ) const;
                void printVariables( bool = true, std::ostream& = std::cout, const std::string = "" ) const;
                #ifdef LRA_REFINEMENT
                void printLearnedBounds( const std::string = "", std::ostream& = std::cout ) const;
                void printLearnedBound( const Variable<T1,T2>&, const LearnedBound&, const std::string = "", std::ostream& = std::cout ) const;
                #endif
                void print( EntryID = LAST_ENTRY_ID, std::ostream& = std::cout, const std::string = "", bool = true, bool = false ) const;

        };

        template<typename T1, typename T2>
        Tableau<T1,T2>::Tableau( std::list<const smtrat::Formula*>::iterator _defaultBoundPosition ):
            mRowsCompressed( true ),
            mWidth( 0 ),
            mPivotingSteps( 0 ),
            #ifdef LRA_USE_PIVOTING_STRATEGY
            mMaxPivotsWithoutBlandsRule( 0 ),
            #endif
            mDefaultBoundPosition( _defaultBoundPosition ),
            mUnusedIDs(),
            mRows(),
            mColumns(),
            mNonActiveBasics(),
            mConflictingRows(),
            mOriginalVars(),
            mSlackVars(),
            mConstraintToBound()
            #ifdef LRA_REFINEMENT
            ,
            mLearnedLowerBounds(),
            mLearnedUpperBounds(),
            mNewLearnedBounds()
            #endif
        {
            mpEntries = new std::vector< TableauEntry<T1,T2> >();
            mpEntries->push_back( TableauEntry<T1,T2>() );
            mpTheta = new Value<T1>();
        };

        template<typename T1, typename T2>
        Tableau<T1,T2>::~Tableau()
        {
            #ifdef LRA_PRINT_STATS
            std::cout << "#Pivoting steps:  " << mPivotingSteps << std::endl;
            std::cout << "#Tableus entries: " << mpEntries->size()-1 << std::endl;
            std::cout << "Tableau coverage: " << (double)(mpEntries->size()-1)/(double)(mRows.size()*mColumns.size())*100 << "%" << std::endl;
            #endif
            while( !mConstraintToBound.empty() )
            {
                std::vector< const Bound<T1,T2>* >* toDelete = mConstraintToBound.begin()->second;
                mConstraintToBound.erase( mConstraintToBound.begin() );
                if( toDelete != NULL ) delete toDelete;
            }
            while( !mOriginalVars.empty() )
            {
                Variable<T1,T2>* varToDelete = mOriginalVars.begin()->second;
                mOriginalVars.erase( mOriginalVars.begin() );
                delete varToDelete;
            }
            while( !mSlackVars.empty() )
            {
                Variable<T1,T2>* varToDelete = mSlackVars.begin()->second;
                mSlackVars.erase( mSlackVars.begin() );
                delete varToDelete;
            }
            delete mpEntries;
            delete mpTheta;
        };

        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        EntryID Tableau<T1,T2>::newTableauEntry( const T2& _content )
        {
            if( mUnusedIDs.empty() )
            {
                mpEntries->push_back( TableauEntry<T1,T2>( LAST_ENTRY_ID, LAST_ENTRY_ID, LAST_ENTRY_ID, LAST_ENTRY_ID, 0, 0, _content ) );
                return ( ( mpEntries->size() ) - 1);
            }
            else
            {
                EntryID id = mUnusedIDs.top();
                mUnusedIDs.pop();
                (*mpEntries)[id].rContent() = _content;
                return id;
            }
        }

        /**
         *
         * @param _entryID
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::removeEntry( EntryID _entryID )
        {
            TableauEntry<T1,T2>& entry = (*mpEntries)[_entryID];
            const EntryID& up = entry.vNext( false );
            const EntryID& down = entry.vNext( true );
            if( up != LAST_ENTRY_ID )
            {
                (*mpEntries)[up].setVNext( true, down );
            }
            if( down != LAST_ENTRY_ID )
            {
                (*mpEntries)[down].setVNext( false, up );
            }
            else
            {
                entry.columnVar()->rStartEntry() = up;
            }
            const EntryID& left = entry.hNext( true );
            const EntryID& right = entry.hNext( false );
            if( left != LAST_ENTRY_ID )
            {
                (*mpEntries)[left].setHNext( false, right );
            }
            else
            {
                entry.rowVar()->rStartEntry() = right;
            }
            if( right != LAST_ENTRY_ID )
            {
                (*mpEntries)[right].setHNext( true, left );
            }
            --(entry.rowVar()->rSize());
            --(entry.columnVar()->rSize());
            mUnusedIDs.push( _entryID );
        }
        
        template<typename T1, typename T2>
        void Tableau<T1,T2>::activateBound( const Bound<T1,T2>* _bound, const PointerSet<Formula>& _formulas )
        {
            _bound->pOrigins()->push_back( _formulas );
            const Variable<T1,T2>& var = _bound->variable();
            if( !var.isActive() && var.isBasic() && !var.isOriginal() )
                activateBasicVar( _bound->pVariable() );
            if( _bound->isUpperBound() )
            {
                if( *var.pSupremum() > *_bound )
                {
                    _bound->pVariable()->setSupremum( _bound );
                    if( !(*var.pInfimum() > _bound->limit() && !_bound->deduced()) && !var.isBasic() && (*var.pSupremum() < var.assignment()) )
                    {
                        updateBasicAssignments( var.position(), Value<T1>( (*var.pSupremum()).limit() - var.assignment() ) );
                        _bound->pVariable()->rAssignment() = (*var.pSupremum()).limit();
                    }
                }
            }
            if( _bound->isLowerBound() )
            {
                if( *var.pInfimum() < *_bound )
                {
                    _bound->pVariable()->setInfimum( _bound );
                    if( !(*var.pSupremum() < _bound->limit() && !_bound->deduced()) && !var.isBasic() && (*var.pInfimum() > var.assignment()) )
                    {
                        updateBasicAssignments( var.position(), Value<T1>( (*var.pInfimum()).limit() - var.assignment() ) );
                        _bound->pVariable()->rAssignment() = (*var.pInfimum()).limit();
                    }
                }
            }
        }
        
        template<typename T1, typename T2>
        std::pair<const Bound<T1,T2>*, bool> Tableau<T1,T2>::newBound( const smtrat::Constraint* _constraint )
        {
            assert( _constraint->isConsistent() == 2 );
            T1 boundValue = T1( 0 );
            bool negative = false;
            Variable<T1, T2>* newVar;
            if( _constraint->lhs().nrTerms() == 1 || ( _constraint->lhs().nrTerms() == 2 && _constraint->lhs().hasConstantTerm() ) )
            {
                auto term = _constraint->lhs().begin();
                for( ; term != _constraint->lhs().end(); ++term )
                    if( !(*term)->isConstant() ) break;
                carl::Variable var = (*(*term)->monomial())[0].var;
                T1 primCoeff = T1( (*term)->coeff() );
                negative = (primCoeff < T1( 0 ));
                boundValue = T1( -_constraint->constantPart() )/primCoeff;
                typename std::map<carl::Variable, Variable<T1, T2>*>::iterator basicIter = mOriginalVars.find( var );
                // constraint not found, add new nonbasic variable
                if( basicIter == mOriginalVars.end() )
                {
                    Polynomial* varPoly = new Polynomial( var );
                    newVar = newNonbasicVariable( varPoly );
                    mOriginalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, newVar ) );
                }
                else
                {
                    newVar = basicIter->second;
                }
            }
            else
            {
                T1 constantPart = T1( _constraint->constantPart() );
                negative = (_constraint->lhs().lterm()->coeff() < T1( 0 ));
                Polynomial* linearPart;
                if( negative )
                    linearPart = new Polynomial( -_constraint->lhs() + (Rational)constantPart );
                else
                    linearPart = new Polynomial( _constraint->lhs() - (Rational)constantPart );
                T1 cf = T1( linearPart->coprimeFactor() );
                assert( cf > 0 );
                constantPart *= cf;
                (*linearPart) *= cf;
                boundValue = (negative ? constantPart : -constantPart);
                typename FastPointerMap<Polynomial, Variable<T1, T2>*>::iterator slackIter = mSlackVars.find( linearPart );
                if( slackIter == mSlackVars.end() )
                {
                    newVar = newBasicVariable( linearPart, mOriginalVars );
                    mSlackVars.insert( std::pair<const Polynomial*, Variable<T1, T2>*>( linearPart, newVar ) );
                }
                else
                {
                    delete linearPart;
                    newVar = slackIter->second;
                }
            }
            std::pair<const Bound<T1,T2>*, bool> result;
            if( _constraint->relation() == Relation::EQ )
            {
                // TODO: Take value from an allocator to assure the values are located close to each other in the memory.
                Value<T1>* value  = new Value<T1>( boundValue );
                result = newVar->addEqualBound( value, mDefaultBoundPosition, _constraint );
                std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                result.first->boundExists();
                boundVector->push_back( result.first );
                mConstraintToBound[_constraint] = boundVector;
            }
            if( _constraint->relation() == Relation::LEQ || ( _constraint->integerValued() && _constraint->relation() == Relation::NEQ ) )
            {   
                const Constraint* constraint;
                Value<T1>* value;
                if( _constraint->integerValued() && _constraint->relation() == Relation::NEQ )
                {
                    constraint = newConstraint( _constraint->lhs(), Relation::LESS );
                    value = new Value<T1>( boundValue - T1( 1 ) );
                }
                else
                {
                    constraint = _constraint;
                    value = new Value<T1>( boundValue );
                }
                if( negative )
                {
                    result = newVar->addLowerBound( value, mDefaultBoundPosition, constraint );
                }
                else
                {
                    result = newVar->addUpperBound( value, mDefaultBoundPosition, constraint );
                }
                std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                result.first->boundExists();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->integerValued() && _constraint->relation() == Relation::NEQ )
                {
                    std::vector< const Bound<T1,T2>* >* boundVectorB = new std::vector< const Bound<T1,T2>* >();
                    boundVectorB->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVectorB;
                    result.first->setNeqRepresentation( _constraint );
                }
                else
                {  
                    result.first->boundExists();
                }
            }
            if( _constraint->relation() == Relation::GEQ || ( _constraint->integerValued() && _constraint->relation() == Relation::NEQ ) )
            {
                const Constraint* constraint;
                Value<T1>* value;
                if( _constraint->integerValued() && _constraint->relation() == Relation::NEQ )
                {
                    constraint = newConstraint( _constraint->lhs(), Relation::GREATER );
                    value = new Value<T1>( boundValue + T1( 1 ) );
                }
                else
                {
                    constraint = _constraint;
                    value = new Value<T1>( boundValue );
                }
                if( negative )
                {
                    result = newVar->addUpperBound( value, mDefaultBoundPosition, constraint );
                }
                else
                {
                    result = newVar->addLowerBound( value, mDefaultBoundPosition, constraint );
                }
                std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->integerValued() && _constraint->relation() == Relation::NEQ )
                {
                    mConstraintToBound[_constraint]->push_back( result.first );
                    result.first->setNeqRepresentation( _constraint );
                }
                else
                {  
                    result.first->boundExists();
                }
            }
            if( _constraint->relation() == Relation::LESS || _constraint->relation() == Relation::NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != Relation::NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = newConstraint( _constraint->lhs(), Relation::LESS );
                }
                Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( 1 ) : T1( -1 ) ) );
                if( negative )
                {
                    result = newVar->addLowerBound( value, mDefaultBoundPosition, constraint );
                }
                else
                {
                    result = newVar->addUpperBound( value, mDefaultBoundPosition, constraint );
                }
                std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == Relation::NEQ )
                {
                    std::vector< const Bound<T1,T2>* >* boundVectorB = new std::vector< const Bound<T1,T2>* >();
                    boundVectorB->push_back( result.first );
                    mConstraintToBound[_constraint] = boundVectorB;
                    result.first->setNeqRepresentation( _constraint );
                }
                else
                {  
                    result.first->boundExists();
                }
            }
            if( _constraint->relation() == Relation::GREATER || _constraint->relation() == Relation::NEQ )
            {
                const Constraint* constraint;
                if( _constraint->relation() != Relation::NEQ )
                {
                    constraint = _constraint;
                }
                else
                {
                    constraint = newConstraint( _constraint->lhs(), Relation::GREATER );
                }
                Value<T1>* value = new Value<T1>( boundValue, (negative ? T1( -1 ) : T1( 1 )) );
                if( negative )
                {
                    result = newVar->addUpperBound( value, mDefaultBoundPosition, constraint );
                }
                else
                {
                    result = newVar->addLowerBound( value, mDefaultBoundPosition, constraint );
                }
                std::vector< const Bound<T1,T2>* >* boundVector = new std::vector< const Bound<T1,T2>* >();
                boundVector->push_back( result.first );
                mConstraintToBound[constraint] = boundVector;
                if( _constraint->relation() == Relation::NEQ )
                {
                    mConstraintToBound[_constraint]->push_back( result.first );
                    result.first->setNeqRepresentation( _constraint );
                }
                else
                {
                    result.first->boundExists();
                }
            }
            return result;
        }
        
        /**
         *
         * @param _ex
         * @return
         */
        template<typename T1, typename T2>
        Variable<T1, T2>* Tableau<T1,T2>::newNonbasicVariable( const smtrat::Polynomial* _poly )
        {
            Variable<T1, T2>* var = new Variable<T1, T2>( mWidth++, _poly, mDefaultBoundPosition );
            mColumns.push_back( var );
            return var;
        }

        /**
         *
         * @param _poly
         * @return
         */
        template<typename T1, typename T2>
        Variable<T1, T2>* Tableau<T1,T2>::newBasicVariable( const smtrat::Polynomial* _poly, std::map<carl::Variable, Variable<T1, T2>*>& _originalVars )
        {
            mNonActiveBasics.emplace_front();
            Variable<T1, T2>* var = new Variable<T1, T2>( mNonActiveBasics.begin(), _poly, mDefaultBoundPosition );
            for( auto term = _poly->begin(); term != _poly->end(); ++term )
            {
                assert( !(*term)->isConstant() );
                assert( carl::isInteger( (*term)->coeff() ) );
                carl::Variable var = (*(*term)->monomial())[0].var;
                Variable<T1, T2>* nonBasic;
                auto nonBasicIter = _originalVars.find( var );
                if( _originalVars.end() == nonBasicIter )
                {
                    Polynomial* varPoly = new Polynomial( var );
                    nonBasic = newNonbasicVariable( varPoly );
                    _originalVars.insert( std::pair<carl::Variable, Variable<T1, T2>*>( var, nonBasic ) );
                }
                else
                {
                    nonBasic = nonBasicIter->second;
                }
                mNonActiveBasics.front().emplace_back( nonBasic, T2( carl::getNum( (*term)->coeff() ) ) );
            }
            return var;
        }
        
        /**
         * 
         * @param _var
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::activateBasicVar( Variable<T1, T2>* _var )
        {
            assert( _var->isBasic() );
            assert( !_var->isOriginal() );
            assert( !_var->isActive() );
            compressRows();
            std::map<size_t,T2> coeffs;
            for( auto lravarCoeffPair = _var->positionInNonActives()->begin(); lravarCoeffPair != _var->positionInNonActives()->end(); ++lravarCoeffPair )
            {
                Variable<T1, T2>* lravar = lravarCoeffPair->first;
                if( lravar->isBasic() )
                {
                    if( !lravar->isActive() && !lravar->isOriginal() )
                    {
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
                            iter->second *= cb;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
                            iterB->second *= cb;
                        }
                        #endif
                        for( auto lravarCoeffPairB = lravar->positionInNonActives()->begin(); lravarCoeffPairB != lravar->positionInNonActives()->end(); ++lravarCoeffPairB )
                        {
                            _var->positionInNonActives()->emplace_back( lravarCoeffPairB->first, ca*lravarCoeffPairB->second );
                        }
                    }
                    else
                    {
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
                            iter->second *= cb;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
                            iterB->second *= cb;
                        }
                        #endif
                        Iterator rowIter = Iterator( lravar->startEntry(), mpEntries );
                        while( true )
                        {
                            coeffs[(*rowIter).columnVar()->position()] += ca*(*rowIter).content();
                            if( rowIter.hEnd( false ) ) break;
                            else rowIter.hMove( false );
                        }
                    }
                }
                else
                {
                    coeffs[lravar->position()] += lravarCoeffPair->second;
                }
            }
            mNonActiveBasics.erase( _var->positionInNonActives() );
            
            T2 g = carl::abs( _var->factor() );
            for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
            {
                if( g == 1 ) break;
                if( iter->second != T2( 0 ) )
                    carl::gcd_here( g, iter->second );
            }
            if( !(g == 1) )
            {
                assert( g > 0 );
                for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter  )
                {
                    if( iter->second != T2( 0 ) )
                        carl::div_here( iter->second, g );
                }
                carl::div_here( _var->rFactor(), g );
            }
            
            _var->setPosition( mRows.size() );
            mRows.push_back( _var );
            _var->rAssignment() = Value<T1>( 0 );
            EntryID lastInsertedEntry = LAST_ENTRY_ID;
            _var->rSize() = 0;
            for( auto coeff = coeffs.begin(); coeff != coeffs.end(); ++coeff  )
            {
                if( coeff->second == T2( 0 ) )
                    continue;
                ++(_var->rSize());
                EntryID entryID = newTableauEntry( coeff->second );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Fix the position.
                entry.setColumnVar( mColumns[coeff->first] );
                entry.setRowVar( _var );
                EntryID& columnStart = mColumns[coeff->first]->rStartEntry();
                // Set it as column end.
                if( columnStart != LAST_ENTRY_ID )
                {
                    (*mpEntries)[columnStart].setVNext( true, entryID );
                }
                entry.setVNext( false, columnStart );
                columnStart = entryID;
                ++(mColumns[coeff->first]->rSize());
                entry.setVNext( true, LAST_ENTRY_ID );
                // Put it in the row.
                if( lastInsertedEntry == LAST_ENTRY_ID )
                {
                    _var->rStartEntry() = entryID;
                    entry.setHNext( true, lastInsertedEntry );
                }
                else
                {
                    Iterator rowIter = Iterator( lastInsertedEntry, mpEntries );
                    // Entry will be the rightmost in this row.
                    (*rowIter).setHNext( false, entryID );
                    entry.setHNext( true, rowIter.entryID() );
                    entry.setHNext( false, LAST_ENTRY_ID );
                }
                lastInsertedEntry = entryID;
                _var->rAssignment() += mColumns[coeff->first]->assignment() * coeff->second;
            }
            _var->rAssignment() /= _var->factor();
            assert( checkCorrectness() == mRows.size() );
        }
        
        /**
         * 
         * @param 
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::deactivateBasicVar( Variable<T1, T2>* _var )
        {
            assert( _var->isBasic() );
            assert( !_var->isOriginal() );
            #ifdef LRA_LOCAL_CONFLICT_DIRECTED
            auto crIter = mConflictingRows.begin();
            for( ; crIter != mConflictingRows.end(); ++crIter )
                if( (*crIter) == _var ) break;
            if( crIter != mConflictingRows.end() )
            {
                mConflictingRows.erase( crIter );
            }
            #endif
            mNonActiveBasics.emplace_front();
            EntryID entryToRemove = _var->startEntry();
            while( entryToRemove != LAST_ENTRY_ID )
            {
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryToRemove];
                Variable<T1, T2>* nbVar = entry.columnVar();
                mNonActiveBasics.front().emplace_back( nbVar, entry.content() );
                EntryID up = entry.vNext( false );
                EntryID down = entry.vNext( true );
                if( up != LAST_ENTRY_ID )
                {
                    (*mpEntries)[up].setVNext( true, down );
                }
                if( down != LAST_ENTRY_ID )
                {
                    (*mpEntries)[down].setVNext( false, up );
                }
                else
                {
                    nbVar->rStartEntry() = up;
                }
                --(nbVar->rSize());
                entry.setRowVar( NULL ); //Not necessary but cleaner.
                mUnusedIDs.push( entryToRemove );
                entryToRemove = entry.hNext( false );
            }
            mRows[_var->position()] = NULL;
            _var->rStartEntry() = LAST_ENTRY_ID;
            _var->rSize() = 0;
            _var->rPosition() = 0;
            _var->setPositionInNonActives( mNonActiveBasics.begin() );
            mRowsCompressed = false;
        }
        
        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::compressRows()
        {
            if( mRowsCompressed ) return;
            std::deque<size_t> emptyPositions;
            size_t curPos = 0;
            while( curPos < mRows.size() )
            {
                if( mRows[curPos] == NULL )
                {
                    emptyPositions.push_back( curPos );
                }
                else if( !emptyPositions.empty() )
                {
                    size_t emptyPos = emptyPositions.front();
                    emptyPositions.pop_front();
                    mRows[emptyPos] = mRows[curPos];
                    mRows[emptyPos]->rPosition() = emptyPos;
                    emptyPositions.push_back( curPos );
                }
                ++curPos;
            }
            mRows.resize( mRows.size() - emptyPositions.size() );
            mRowsCompressed = true;
        }

        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<T1,T2>::nextPivotingElement()
        {
            #ifdef LRA_USE_PIVOTING_STRATEGY
            //  Dynamic strategy for a fixed number of steps
            if( mPivotingSteps < mMaxPivotsWithoutBlandsRule )
            {
#ifdef LRA_LOCAL_CONFLICT_DIRECTED
FindPivot:
#endif
                EntryID bestTableauEntry = LAST_ENTRY_ID;
                EntryID beginOfFirstConflictRow = LAST_ENTRY_ID;
                #ifdef LRA_USE_THETA_STRATEGY
                Value<T1> bestDiff = Value<T1>( 0 );
                #endif
                Value<T1> bestThetaB = Value<T1>( 0 );
                #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                bool initialSearch = mConflictingRows.empty();
                std::vector<Variable<T1,T2>*>& rowsToConsider = initialSearch ? mRows : mConflictingRows;
                #else
                std::vector<Variable<T1,T2>*>& rowsToConsider = mRows;
                #endif 
                typename std::vector<Variable<T1,T2>*>::iterator bestVar = rowsToConsider.end();
                for( auto basicVar = rowsToConsider.begin(); basicVar != rowsToConsider.end(); )
                {
                    assert( *basicVar != NULL );
                    Variable<T1,T2>& bVar = **basicVar;
                    #ifdef LRA_USE_THETA_STRATEGY
                    Value<T1> diff = Value<T1>( 0 );
                    #endif
                    Value<T1> thetaB = Value<T1>( 0 );
                    bool upperBoundViolated = false;
                    bool lowerBoundViolated = false;
                    if( bVar.supremum() < bVar.assignment() )
                    {
                        thetaB = bVar.supremum().limit() - bVar.assignment();
                        #ifdef LRA_USE_THETA_STRATEGY
                        diff = thetaB * T2(-1);
                        #endif
                        upperBoundViolated = true;
                    }
                    else if( bVar.infimum() > bVar.assignment() )
                    {
                        thetaB = bVar.infimum().limit() - bVar.assignment();
                        #ifdef LRA_USE_THETA_STRATEGY
                        diff = thetaB;
                        #endif
                        lowerBoundViolated = true;
                    }
                    else
                    {
                        #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                        if( !initialSearch )
                        {
                            bool resetBestVarToEnd = bestVar == mConflictingRows.end();
                            basicVar = mConflictingRows.erase( basicVar );
                            if( resetBestVarToEnd ) bestVar = mConflictingRows.end();
                            if( mConflictingRows.empty() )
                            {
                                goto FindPivot;
                            }
                        }
                        else
                        {
                            ++basicVar;
                        }
                        #else
                        ++basicVar;
                        #endif
                        continue;
                    }
                    #ifdef LRA_USE_THETA_STRATEGY
                    if( diff <= bestDiff )
                    {
                        ++basicVar;
                        continue;
                    }
                    #endif
                    #ifdef LRA_USE_ACTIVITY_STRATEGY
                    if( (*basicVar)->conflictActivity() <= (*bestVar)->conflictActivity() )
                    {
                        ++basicVar;
                        continue;
                    }
                    #endif
                    if( upperBoundViolated || lowerBoundViolated )
                    {
                        std::pair<EntryID,bool> result = isSuitable( bVar, upperBoundViolated );
                        if( !result.second )
                        {
                            bestTableauEntry = LAST_ENTRY_ID;
                            // Found a conflicting row.
                            if( beginOfFirstConflictRow == LAST_ENTRY_ID )
                            {
                                beginOfFirstConflictRow = result.first;
                                bestVar = basicVar;
                                break;
                            }
                        }
                        else if( result.first != LAST_ENTRY_ID )
                        {
                            if( bestVar == rowsToConsider.end() )
                            {
                                bestTableauEntry = result.first;
                                bestVar = basicVar;
                                #ifdef LRA_USE_THETA_STRATEGY
                                bestDiff = diff;
                                #endif
                                bestThetaB = thetaB;
                            }
                            else
                            {
                                assert( result.first != LAST_ENTRY_ID );
                                assert( bestVar != rowsToConsider.end() );
                                assert( bestTableauEntry != LAST_ENTRY_ID );
                                #ifdef LRA_EQUATION_FIRST
                                if( !(*bestVar)->involvesEquation() && bVar.involvesEquation() )
                                {
                                    bestTableauEntry = result.first;
                                    bestVar = basicVar;
                                }
                                else if( (*bestVar)->involvesEquation() || !bVar.involvesEquation() )
                                {
                                #endif
                                    bestTableauEntry = result.first;
                                    bestThetaB = thetaB;
                                    #ifdef LRA_USE_THETA_STRATEGY
                                    bestDiff = diff;
                                    #endif
                                    #ifdef LRA_EQUATION_FIRST
                                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                                    if( initialSearch && (*bestVar)->involvesEquation() )
                                        mConflictingRows.push_back( *bestVar );
                                    #endif
                                    #endif
                                    bestVar = basicVar;
                                #ifdef LRA_EQUATION_FIRST
                                }
                                #endif
                            }
                        }
                    }
                    ++basicVar;
                }
                if( bestTableauEntry == LAST_ENTRY_ID && beginOfFirstConflictRow != LAST_ENTRY_ID )
                {
                    // Found a conflict
                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                    mConflictingRows.clear();
                    #endif
                    return std::pair<EntryID,bool>( beginOfFirstConflictRow, false );
                }
                else if( bestTableauEntry != LAST_ENTRY_ID )
                {
                    // The best pivoting element found
                    *mpTheta = bestThetaB;
                    #ifdef LRA_NO_DIVISION
                    (*mpTheta) *= (*bestVar)->factor();
                    #endif 
                    (*mpTheta) /= (*mpEntries)[bestTableauEntry].content();
                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                    if( !initialSearch )
                    {
                        assert( bestVar != mConflictingRows.end() );
                        mConflictingRows.erase( bestVar );
                    }
                    #endif
                    return std::pair<EntryID,bool>( bestTableauEntry, true );
                }
                else
                {
                    // Found no pivoting element, that is no variable violates its bounds.
                    assert( mConflictingRows.empty() );
                    return std::pair<EntryID,bool>( LAST_ENTRY_ID, true );
                }
            }
            // Bland's rule
            else
            {
            #endif
                for( const Variable<T1, T2>* basicVar : mRows )
                {
                    assert( basicVar != NULL );
                    const Variable<T1,T2>& bVar = *basicVar;
                    Value<T1> thetaB = Value<T1>( 0 );
                    bool upperBoundViolated = false;
                    bool lowerBoundViolated = false;
                    if( bVar.supremum() < bVar.assignment() )
                    {
                        thetaB = bVar.supremum().limit() - bVar.assignment();
                        upperBoundViolated = true;
                    }
                    else if( bVar.infimum() > bVar.assignment() )
                    {
                        thetaB = bVar.infimum().limit() - bVar.assignment();
                        lowerBoundViolated = true;
                    }
                    if( upperBoundViolated || lowerBoundViolated )
                    {
                        std::pair<EntryID,bool> result = isSuitable( bVar, upperBoundViolated );
                        if( !result.second )
                        {
                            // Found a conflicting row.
                            return std::pair<EntryID,bool>( result.first, false );
                        }
                        else if( result.first != LAST_ENTRY_ID )
                        {
                            // Found a pivoting element
                            *mpTheta = thetaB;
                            #ifdef LRA_NO_DIVISION
                            (*mpTheta) *= bVar.factor();
                            #endif 
                            (*mpTheta) /= (*mpEntries)[result.first].content();
                            return std::pair<EntryID,bool>( result.first, true );
                        }
                    }
                }
                // Found no pivoting element, that is no variable violates its bounds.
                return std::pair<EntryID,bool>( LAST_ENTRY_ID, true );
            #ifdef LRA_USE_PIVOTING_STRATEGY
            }
            #endif
        }

        /**
         * @param _rowNumber
         * @return
         */
        template<typename T1, typename T2>
        std::pair<EntryID,bool> Tableau<T1,T2>::isSuitable( const Variable<T1, T2>& _basicVar, bool supremumViolated ) const
        {
            EntryID bestEntry = LAST_ENTRY_ID;
            const Bound<T1, T2>& basicVarSupremum = _basicVar.supremum();
            const Value<T1>& basicVarAssignment = _basicVar.assignment();
            const Bound<T1, T2>& basicVarInfimum = _basicVar.infimum();
            EntryID rowStartEntry = _basicVar.startEntry();
            // Upper bound is violated
            if( supremumViolated )
            {
                assert( basicVarSupremum < basicVarAssignment );
                // Check all entries in the row / nonbasic variables
                Iterator rowIter = Iterator( rowStartEntry, mpEntries );
                while( true )
                {
                    const Variable<T1, T2>& nonBasicVar = *(*rowIter).columnVar();
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() < 0 && _basicVar.factor() > 0) || ((*rowIter).content() > 0 && _basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() < 0 )
                    #endif
                    {
                        if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    else
                    {
                        if( nonBasicVar.infimum() < nonBasicVar.assignment()  )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            return std::pair<EntryID,bool>( rowStartEntry, false );
                        }
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            // Lower bound is violated
            else
            {
                assert( basicVarInfimum > basicVarAssignment );
                // Check all entries in the row / nonbasic variables
                Iterator rowIter = Iterator( rowStartEntry, mpEntries );
                while( true )
                {
                    const Variable<T1, T2>& nonBasicVar = *(*rowIter).columnVar();
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() > 0 && _basicVar.factor() > 0) || ((*rowIter).content() < 0 && _basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() > 0 )
                    #endif
                    {
                        if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    else
                    {
                        if( nonBasicVar.infimum() < nonBasicVar.assignment() )
                        {
                            // Nonbasic variable suitable
                            assert( (*rowIter).content() != 0 );
                            if( betterEntry( rowIter.entryID(), bestEntry ) )
                            {
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            return std::pair<EntryID,bool>( rowStartEntry, false );
                        }
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            return std::pair<EntryID,bool>( bestEntry, true );
        }

        template<typename T1, typename T2>
        bool Tableau<T1,T2>::betterEntry( EntryID _isBetter, EntryID _than ) const
        {
            assert( _isBetter != LAST_ENTRY_ID );
            if( _than == LAST_ENTRY_ID ) return true;
            const Variable<T1,T2>& isBetterNbVar = *((*mpEntries)[_isBetter].columnVar());
            const Variable<T1,T2>& thanColumnNbVar = *((*mpEntries)[_than].columnVar());
            size_t valueA = boundedVariables( isBetterNbVar );
            size_t valueB = boundedVariables( thanColumnNbVar, valueA );
            if( valueA < valueB  ) return true;
            else if( valueA == valueB )
            {
                if( isBetterNbVar.size() < thanColumnNbVar.size() ) return true;
            }
            return false;
        }

        /**
         *
         * @param _startRow
         * @return
         */
        template<typename T1, typename T2>
        std::vector< const Bound<T1, T2>* > Tableau<T1,T2>::getConflict( EntryID _rowEntry ) const
        {
            assert( _rowEntry != LAST_ENTRY_ID );
            const Variable<T1,T2>& basicVar = *((*mpEntries)[_rowEntry].rowVar());
            // Upper bound is violated
            std::vector< const Bound<T1, T2>* > conflict = std::vector< const Bound<T1, T2>* >();
            if( basicVar.supremum() < basicVar.assignment() )
            {
                conflict.push_back( basicVar.pSupremum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() < 0 )
                    #endif
                    {
                        assert( !((*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pSupremum() );
                    }
                    else
                    {
                        assert( !((*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pInfimum() );
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            // Lower bound is violated
            else
            {
                assert( basicVar.infimum() > basicVar.assignment() );
                conflict.push_back( basicVar.pInfimum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    #ifdef LRA_NO_DIVISION
                    if( ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0) )
                    #else
                    if( (*rowIter).content() > 0 )
                    #endif
                    {
                        assert( !((*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pSupremum() );
                    }
                    else
                    {
                        assert( !((*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()) );
                        conflict.push_back( (*rowIter).columnVar()->pInfimum() );
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.hMove( false );
                    }
                }
            }
            return conflict;
        }

        /**
         *
         * @param _startRow
         * @return
         */
        template<typename T1, typename T2>
        std::vector< std::set< const Bound<T1, T2>* > > Tableau<T1,T2>::getConflictsFrom( EntryID _rowEntry ) const
        {
            std::vector< std::set< const Bound<T1, T2>* > > conflicts = std::vector< std::set< const Bound<T1, T2>* > >();
            const Variable<T1,T2>* firstConflictingVar = (*mpEntries)[_rowEntry].rowVar();
            bool posOfFirstConflictFound = false;
            for( Variable<T1,T2>* rowElement : mRows )
            {
                if( !posOfFirstConflictFound && rowElement != firstConflictingVar )
                    continue;
                assert( rowElement != NULL );
                // Upper bound is violated
                const Variable<T1,T2>& basicVar = *rowElement;
                if( basicVar.supremum() < basicVar.assignment() )
                {
                    conflicts.push_back( std::set< const Bound<T1, T2>* >() );
                    conflicts.back().insert( basicVar.pSupremum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( ( (*rowIter).content() < 0 && basicVar.factor() > 0) || ((*rowIter).content() > 0 && basicVar.factor() < 0) )
                        #else
                        if( (*rowIter).content() < 0 )
                        #endif
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment() )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pSupremum() );
                            }
                        }
                        else
                        {
                            if( (*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment() )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pInfimum() );
                            }
                        }
                        if( rowIter.hEnd( false ) )
                        {
                            break;
                        }
                        else
                        {
                            rowIter.hMove( false );
                        }
                    }
                }
                // Lower bound is violated
                else if( basicVar.infimum() > basicVar.assignment() )
                {
                    conflicts.push_back( std::set< const Bound<T1, T2>* >() );
                    conflicts.back().insert( basicVar.pInfimum() );
                    // Check all entries in the row / basic variables
                    Iterator rowIter = Iterator( basicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        #ifdef LRA_NO_DIVISION
                        if( ((*rowIter).content() > 0 && basicVar.factor() > 0) || ((*rowIter).content() < 0 && basicVar.factor() < 0) )
                        #else
                        if( (*rowIter).content() > 0 )
                        #endif
                        {
                            if( (*rowIter).columnVar()->supremum() > (*rowIter).columnVar()->assignment()  )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pSupremum() );
                            }
                        }
                        else
                        {
                            if( (*rowIter).columnVar()->infimum() < (*rowIter).columnVar()->assignment()  )
                            {
                                // Not a conflict.
                                conflicts.pop_back();
                                break;
                            }
                            else
                            {
                                conflicts.back().insert( (*rowIter).columnVar()->pInfimum() );
                            }
                        }
                        if( rowIter.hEnd( false ) )
                        {
                            break;
                        }
                        else
                        {
                            rowIter.hMove( false );
                        }
                    }
                }
            }
            return conflicts;
        }

        /**
         *
         * @param _column
         * @param _change
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::updateBasicAssignments( size_t _column, const Value<T1>& _change )
        {
            Variable<T1,T2>& nonbasicVar = *mColumns[_column];
            if( nonbasicVar.size() > 0 )
            {
                Iterator columnIter = Iterator( nonbasicVar.startEntry(), mpEntries );
                while( true )
                {
                    Variable<T1, T2>& basic = *((*columnIter).rowVar());
                    #ifdef LRA_NO_DIVISION
                    basic.rAssignment() += (_change * (*columnIter).content())/basic.factor();
                    #else
                    basic.rAssignment() += (_change * (*columnIter).content());
                    #endif
                    if( columnIter.vEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        columnIter.vMove( false );
                    }
                }
            }
        }

        /**
         *
         * @param _pivotingElement
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::pivot( EntryID _pivotingElement )
        {
            // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
            // First the column with ** left to the pivoting column until the leftmost column with **.
            std::vector<Iterator> pivotingRowLeftSide = std::vector<Iterator>();
            TableauEntry<T1,T2>& pivotEntry = (*mpEntries)[_pivotingElement];
            T2& pivotContent = pivotEntry.rContent();
            Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
            Variable<T1, T2>* rowVar = pivotEntry.rowVar();
            Variable<T1, T2>* columnVar = pivotEntry.columnVar();
            pivotEntry.setRowVar( columnVar );
            Iterator colIter = Iterator( columnVar->startEntry(), mpEntries );
            while( true )
            {
                (*colIter).setColumnVar( rowVar );
                if( colIter.vEnd( false ) )
                    break;
                colIter.vMove( false );
            }
            while( !iterTemp.hEnd( true ) )
            {
                iterTemp.hMove( true );
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowLeftSide.push_back( iterTemp );
            }
            // Then the column with ** right to the pivoting column until the rightmost column with **.
            std::vector<Iterator> pivotingRowRightSide = std::vector<Iterator>();
            iterTemp = Iterator( _pivotingElement, mpEntries );
            while( !iterTemp.hEnd( false ) )
            {
                iterTemp.hMove( false );
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowRightSide.push_back( iterTemp );
            }
            // Swap the variables
            mRows[rowVar->position()] = columnVar;
            mColumns[columnVar->position()] = rowVar;
            // Update the assignments of the pivoting variables
            #ifdef LRA_NO_DIVISION
            rowVar->rAssignment() += ((*mpTheta) * pivotContent) / rowVar->factor();
            #else
            rowVar->rAssignment() += (*mpTheta) * pivotContent;
            #endif
            if( !( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() ) ) 
            {
                std::cout << "rowVar->assignment() = " << rowVar->assignment() << std::endl;
                std::cout << "rowVar->supremum() = " << rowVar->supremum() << std::endl; 
                std::cout << "(error: " << __func__ << " " << __LINE__ << ")" << std::endl; 
//                exit( 7771 );
            }
            assert( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() );
            if( !( rowVar->infimum() < rowVar->assignment() || rowVar->infimum() == rowVar->assignment() ) ) 
            {
                std::cout << "rowVar->assignment() = " << rowVar->assignment() << std::endl;
                std::cout << "rowVar->infimum() = " << rowVar->infimum() << std::endl;
                std::cout << "(error: " << __func__ << " " << __LINE__ << ")" << std::endl; 
//                exit( 7771 );
            }
            assert( rowVar->infimum() < rowVar->assignment() || rowVar->infimum() == rowVar->assignment() );
            columnVar->rAssignment() += (*mpTheta);
            // Adapt both variables.
            Variable<T1, T2>& basicVar = *columnVar;
            Variable<T1, T2>& nonbasicVar = *rowVar;
            size_t tmpPosition = basicVar.position();
            basicVar.rPosition() = nonbasicVar.position();
            nonbasicVar.rPosition() = tmpPosition;
            size_t tmpSize = basicVar.size();
            basicVar.rSize() = nonbasicVar.size();
            nonbasicVar.rSize() = tmpSize;
            basicVar.setBasic( true );
            nonbasicVar.setBasic( false );
            EntryID tmpStartEntry = basicVar.startEntry();
            basicVar.rStartEntry() = nonbasicVar.startEntry();
            nonbasicVar.rStartEntry() = tmpStartEntry;
            #ifdef LRA_NO_DIVISION
            basicVar.rFactor() = pivotContent;
            #endif
            // Update the content of the pivoting entry
            #ifdef LRA_NO_DIVISION
            pivotContent = nonbasicVar.factor();
            nonbasicVar.rFactor() = 1;
            #else
            pivotContent = carl::div( T2(1), pivotContent );
            #endif
            #ifdef LRA_REFINEMENT
            if( basicVar.isActive() || basicVar.isOriginal() )
            {
                rowRefinement( columnVar ); // Note, we have swapped the variables, so the current basic var is now corresponding to what we have stored in columnVar.
            }
            #endif
            // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
            // For all rows R having a nonzero entry in the pivoting column:
            //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
            //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
            if( pivotEntry.vNext( false ) == LAST_ENTRY_ID )
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
            }
            else if( pivotEntry.vNext( true ) == LAST_ENTRY_ID )
            {
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
            }
            else
            {
                update( true, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
                update( false, _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
            }
            ++mPivotingSteps;
            if( !basicVar.isActive() && !basicVar.isOriginal() )
            {
                deactivateBasicVar( columnVar );
                compressRows();
            }
            assert( basicVar.supremum() >= basicVar.assignment() || basicVar.infimum() <= basicVar.assignment() );
            assert( nonbasicVar.supremum() == nonbasicVar.assignment() || nonbasicVar.infimum() == nonbasicVar.assignment() );
            assert( checkCorrectness() == mRows.size() );
        }

        /**
         * Updates the tableau according to the new values in the pivoting row containing the given pivoting element. The updating is
         * applied from the pivoting row downwards, if the given flag _downwards is true, and upwards, otherwise.
         * 
         * @param _downwards The flag indicating whether to update the tableau downwards or upwards starting from the pivoting row.
         * @param _pivotingElement The id of the current pivoting element.
         * @param _pivotingRowLeftSide For every element in the pivoting row, which is positioned left of the pivoting element, this 
         *                              vector contains an iterator. The closer the element is to the pivoting element, the smaller is the 
         *                              iterator's index in the vector.
         * @param _pivotingRowRightSide For every element in the pivoting row, which is positioned right of the pivoting element, this 
         *                              vector contains an iterator. The closer the element is to the pivoting element, the smaller is the 
         *                              iterator's index in the vector.
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::update( bool _downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide )
        {
            std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
            std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
            Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
            #ifdef LRA_NO_DIVISION
            const T2& pivotingRowFactor = (*mpEntries)[_pivotingElement].rowVar()->factor();
            #endif
            while( true )
            {
                if( !pivotingColumnIter.vEnd( _downwards ) )
                {
                    pivotingColumnIter.vMove( _downwards );
                }
                else
                {
                    break;
                }
                // Update the assignment of the basic variable corresponding to this row
                Variable<T1,T2>& currBasicVar = *((*pivotingColumnIter).rowVar());
                #ifdef LRA_NO_DIVISION
                currBasicVar.rAssignment() += ((*mpTheta) * (*pivotingColumnIter).content())/currBasicVar.factor();
                #else
                currBasicVar.rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
                #endif
                // Update the row
                Iterator currentRowIter = pivotingColumnIter;
                #ifdef LRA_NO_DIVISION
                T2 l = carl::lcm( (*pivotingColumnIter).content(), pivotingRowFactor );
                assert( l > 0 );
                if( (*pivotingColumnIter).content() < 0 && pivotingRowFactor < 0 )
                    l *= T2( -1 );
                T2 ca = carl::div( l, pivotingRowFactor );
                T2 cb = carl::div( l, (*pivotingColumnIter).content() );
                currBasicVar.rFactor() *= cb;
                Iterator rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                while( true )
                {
                    (*rowIter).rContent() *= cb;
                    if( rowIter.hEnd( false ) ) break;
                    rowIter.hMove( false );
                }
                T2 g = carl::abs( currBasicVar.factor() );
                #endif
                auto pivotingRowIter = _pivotingRowLeftSide.begin();
                for( auto currentColumnIter = leftColumnIters.begin(); currentColumnIter != leftColumnIters.end(); ++currentColumnIter )
                {
                    assert( pivotingRowIter != _pivotingRowLeftSide.end() );
                    while( (_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position()) 
                           || (!_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( _downwards );
                    }
                    while( !currentRowIter.hEnd( true ) && (*currentRowIter).columnVar()->position() > (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( true );
                    }
                    #ifdef LRA_NO_DIVISION
                    addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
                    #else
                    addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, _downwards );
                    #endif
                    ++pivotingRowIter;
                }
                currentRowIter = pivotingColumnIter;
                pivotingRowIter = _pivotingRowRightSide.begin();
                for( auto currentColumnIter = rightColumnIters.begin(); currentColumnIter != rightColumnIters.end(); ++currentColumnIter )
                {
                    assert( pivotingRowIter != _pivotingRowRightSide.end() );
                    while( (_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position())
                           || (!_downwards && !(*currentColumnIter).vEnd( _downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( _downwards );
                    }
                    while( !currentRowIter.hEnd( false ) && (*currentRowIter).columnVar()->position() < (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( false );
                    }
                    #ifdef LRA_NO_DIVISION
                    addToEntry( ca * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    #else
                    addToEntry( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, _downwards );
                    #endif
                    ++pivotingRowIter;
                }
                #ifdef LRA_NO_DIVISION
                (*pivotingColumnIter).rContent() = ca * (*mpEntries)[_pivotingElement].content();
                rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                while( !(g == 1) )
                {
                    carl::gcd_here( g, (*rowIter).content() );
                    if( rowIter.hEnd( false ) ) break;
                    rowIter.hMove( false );
                }
                if( !(g == 1) )
                {
                    assert( g > 0 );
                    rowIter = Iterator( currBasicVar.startEntry(), mpEntries );
                    while( true )
                    {
                        carl::div_here( (*rowIter).rContent(), g );
                        if( rowIter.hEnd( false ) ) break;
                        else rowIter.hMove( false );
                    }
                    carl::div_here( currBasicVar.rFactor(), g );
                }
                #else
                (*pivotingColumnIter).rContent() *= (*mpEntries)[_pivotingElement].content();
                #endif
                if( currBasicVar.supremum() > currBasicVar.assignment() || currBasicVar.infimum() < currBasicVar.assignment() )
                {
                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                    mConflictingRows.push_back( (*pivotingColumnIter).rowVar() );
                    #endif
                    #ifdef LRA_REFINEMENT
                    rowRefinement( (*pivotingColumnIter).rowVar() );
                    #endif
                }
            }
        }
        
        /**
         * Adds the given value to the entry being at the position (i,j), where i is the vertical position of the given horizontal 
         * iterator and j is the horizontal position of the given vertical iterator. Note, that the entry might not exist, if its
         * current value is 0. Then the horizontal iterator is located horizontally before or after the entry to change and the 
         * vertical iterator is located vertically before or after the entry to add.
         * 
         * @param _toAdd The value to add to the content of the entry specified by the given iterators and their relative position
         *                to each other.
         * @param _horiIter The iterator moving horizontally and, hence, giving the vertical position of the entry to add the given value to.
         * @param _horiIterLeftFromVertIter true, if the horizontally moving iterator is left from or equal to the horizontal position of the
         *                                         iterator moving vertically, and, hence, left from or equal to the position of the entry to add
         *                                         the given value to;
         *                                   false, it is right or equal to this position.
         * @param _vertIter The iterator moving vertically and, hence, giving the horizontal position of the entry to add the given value to.
         * @param _vertIterBelowHoriIter true, if the vertically moving iterator is below or exactly at the vertical position of the
         *                                      iterator moving horizontally, and, hence, below or exactly at the position of the entry to add
         *                                      the given value to;
         *                                false, it is above or equal to this position.
         * @sideeffect If the entry existed (!=0) and is removed because of becoming 0, the iterators are set according to the given relative
         *               positioning.
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::addToEntry( const T2& _toAdd, Iterator& _horiIter, bool _horiIterLeftFromVertIter, Iterator& _vertIter, bool _vertIterBelowHoriIter )
        {
            if( _horiIter == _vertIter )
            {
                // Entry already exists, so update it only and maybe remove it.
                T2& currentRowContent = (*_horiIter).rContent();
                #ifdef LRA_NO_DIVISION
                currentRowContent += _toAdd;
                #else
                currentRowContent += _toAdd;
                #endif
                if( currentRowContent == 0 )
                {
                    EntryID toRemove = _horiIter.entryID();
                    _vertIter.vMove( !_vertIterBelowHoriIter );
                    _horiIter.hMove( !_horiIterLeftFromVertIter );
                    removeEntry( toRemove );
                }
            }
            else
            {
                EntryID entryID = newTableauEntry( _toAdd );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Set the position.
                Variable<T1,T2>* basicVar = (*mpEntries)[_horiIter.entryID()].rowVar();
                Variable<T1,T2>* nonbasicVar = (*mpEntries)[_vertIter.entryID()].columnVar();
                entry.setRowVar( basicVar );
                entry.setColumnVar( nonbasicVar );
                if( (_vertIterBelowHoriIter && (*_vertIter).rowVar()->position() > (*_horiIter).rowVar()->position())
                    || (!_vertIterBelowHoriIter && (*_vertIter).rowVar()->position() < (*_horiIter).rowVar()->position()) )
                {
                    // Entry vertically between two entries.
                    EntryID upperEntryID = (*_vertIter).vNext( !_vertIterBelowHoriIter );
                    if( upperEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[upperEntryID].setVNext( _vertIterBelowHoriIter, entryID );
                    }
                    (*_vertIter).setVNext( !_vertIterBelowHoriIter, entryID );
                    entry.setVNext( !_vertIterBelowHoriIter, upperEntryID );
                    entry.setVNext( _vertIterBelowHoriIter, _vertIter.entryID() );
                }
                else
                {
                    // Entry will be the lowest in this column.
                    (*_vertIter).setVNext( _vertIterBelowHoriIter, entryID );
                    entry.setVNext( !_vertIterBelowHoriIter, _vertIter.entryID() );
                    entry.setVNext( _vertIterBelowHoriIter, LAST_ENTRY_ID );
                    if( _vertIterBelowHoriIter )
                        nonbasicVar->rStartEntry() = entryID;
                }
                if( (_horiIterLeftFromVertIter && (*_horiIter).columnVar()->position() < (*_vertIter).columnVar()->position())
                    || (!_horiIterLeftFromVertIter && (*_horiIter).columnVar()->position() > (*_vertIter).columnVar()->position()) )
                {
                    // Entry horizontally between two entries.
                    EntryID rightEntryID = (*_horiIter).hNext( !_horiIterLeftFromVertIter );
                    if( rightEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[rightEntryID].setHNext( _horiIterLeftFromVertIter, entryID );
                    }
                    (*_horiIter).setHNext( !_horiIterLeftFromVertIter, entryID );
                    entry.setHNext( !_horiIterLeftFromVertIter, rightEntryID );
                    entry.setHNext( _horiIterLeftFromVertIter, _horiIter.entryID() );
                }
                else
                {
                    // Entry will be the leftmost in this row.
                    (*_horiIter).setHNext( _horiIterLeftFromVertIter, entryID );
                    entry.setHNext( !_horiIterLeftFromVertIter, _horiIter.entryID() );
                    entry.setHNext( _horiIterLeftFromVertIter, LAST_ENTRY_ID );
                    if( _horiIterLeftFromVertIter )
                        basicVar->rStartEntry() = entryID;
                }
                // Set the content of the entry.
                ++(basicVar->rSize());
                ++(nonbasicVar->rSize());
            }
        }

        #ifdef LRA_REFINEMENT
        /**
         * Tries to refine the supremum and infimum of the given basic variable. 
         * @param _basicVar The basic variable for which to refine the supremum and infimum.
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::rowRefinement( Variable<T1,T2>* _basicVar )
        {
            /*
             * Collect the bounds which form an upper resp. lower refinement.
             */
            const Variable<T1,T2>& basicVar = *_basicVar; 
            if( basicVar.size() > 128 ) return;
            std::vector<const Bound<T1, T2>*>* uPremise = new std::vector<const Bound<T1, T2>*>();
            std::vector<const Bound<T1, T2>*>* lPremise = new std::vector<const Bound<T1, T2>*>();
            Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
            #ifdef LRA_NO_DIVISION
            const T2& rowFactor = basicVar.factor();
            #endif
            while( true )
            {
                #ifdef LRA_NO_DIVISION
                if( ((*rowEntry).content() > 0 && rowFactor > 0) || ((*rowEntry).content() < 0 && rowFactor < 0) )
                #else
                if( (*rowEntry).content() > 0 )
                #endif
                {
                    if( uPremise != NULL )
                    {
                        const Bound<T1, T2>* sup = (*rowEntry).columnVar()->pSupremum();
                        if( sup->pLimit() != NULL )
                        {
                            uPremise->push_back( sup );
                        }
                        else
                        {
                            delete uPremise;
                            uPremise = NULL;
                            if( lPremise == NULL ) return;
                        }
                    }
                    if( lPremise != NULL )
                    {
                        const Bound<T1, T2>* inf = (*rowEntry).columnVar()->pInfimum();
                        if( inf->pLimit() != NULL )
                        {
                            lPremise->push_back( inf );
                        }
                        else
                        {
                            delete lPremise;
                            lPremise = NULL;
                            if( uPremise == NULL ) return;
                        }
                    }
                }
                else
                {
                    if( uPremise != NULL )
                    {
                        const Bound<T1, T2>* inf = (*rowEntry).columnVar()->pInfimum();
                        if( inf->pLimit() != NULL )
                        {
                            uPremise->push_back( inf );
                        }
                        else
                        {
                            delete uPremise;
                            uPremise = NULL;
                            if( lPremise == NULL ) return;
                        }
                    }
                    if( lPremise != NULL )
                    {
                        const Bound<T1, T2>* sup = (*rowEntry).columnVar()->pSupremum();
                        if( sup->pLimit() != NULL )
                        {
                            lPremise->push_back( sup );
                        }
                        else
                        {
                            delete lPremise;
                            lPremise = NULL;
                            if( uPremise == NULL ) return;
                        }
                    }
                }
                if( rowEntry.hEnd( false ) ) break;
                else rowEntry.hMove( false );
            }
            if( uPremise != NULL )
            {
                /*
                 * Found an upper refinement.
                 */
                Value<T1>* newlimit = new Value<T1>();
                typename std::vector< const Bound<T1, T2>* >::iterator bound = uPremise->begin();
                Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    *newlimit += (*bound)->limit() * (*rowEntry).content();
                    ++bound;
                    if( !rowEntry.hEnd( false ) ) rowEntry.hMove( false );
                    else break;
                }
                /*
                 * Learn that the strongest weaker upper bound should be activated.
                 */
                const typename Bound<T1, T2>::BoundSet& upperBounds = basicVar.upperbounds();
                auto ubound = upperBounds.begin();
                while( ubound != upperBounds.end() )
                {
                    #ifdef LRA_NO_DIVISION
                    if( **ubound > (*newlimit)/rowFactor && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced() )
                    #else
                    if( **ubound > *newlimit && (*ubound)->type() != Bound<T1, T2>::EQUAL && !(*ubound)->deduced() )
                    #endif
                    {
                        break;
                    }
                    if( *ubound == basicVar.pSupremum() )
                    {
                        delete newlimit;
                        delete uPremise;
                        goto CheckLowerPremise;
                    }
                    ++ubound;
                }
                if( ubound != --upperBounds.end() )
                {
                    assert( ((*ubound)->type() != Bound<T1, T2>::EQUAL) );
                    LearnedBound learnedBound = LearnedBound();
                    learnedBound.nextWeakerBound = *ubound;
                    learnedBound.premise = std::vector<const Bound<T1, T2>*>( std::move( *uPremise ) );
                    delete uPremise;
                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                    #ifdef LRA_NO_DIVISION
                    if( newlimit->mainPart() > (*ubound)->limit().mainPart()*rowFactor || (*ubound)->limit().deltaPart() == 0 )
                    #else
                    if( newlimit->mainPart() > (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                    #endif
                    {
                        #ifdef LRA_NO_DIVISION
                        smtrat::Polynomial lhs = (*ubound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart();
                        #else
                        smtrat::Polynomial lhs = (*ubound)->variable().expression() - (Rational)newlimit->mainPart();
                        #endif
                        smtrat::Relation rel = newlimit->deltaPart() != 0 ? smtrat::Relation::LESS : smtrat::Relation::LEQ;
                        const smtrat::Constraint* constraint = smtrat::newConstraint( lhs, rel );
                        learnedBound.newBound = basicVar.addUpperBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                    }
                    else
                    {
                        learnedBound.newBound = NULL;
                    }
                    #else
                    delete newlimit;
                    learnedBound.newBound = NULL;
                    #endif
                    std::pair<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator, bool> insertionResult = mLearnedUpperBounds.insert( std::pair<Variable<T1, T2>*, LearnedBound>( _basicVar, learnedBound ) );
                    if( !insertionResult.second )
                    {
                        if( *learnedBound.nextWeakerBound < *insertionResult.first->second.nextWeakerBound )
                        {
                            insertionResult.first->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            insertionResult.first->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( insertionResult.first );
                        }
                    }
                    else
                    {
                        mNewLearnedBounds.push_back( insertionResult.first );
                    }
                }
                else
                {
                    delete newlimit;
                    delete uPremise;
                }
            }
    CheckLowerPremise:
            if( lPremise != NULL )
            {
                /*
                 * Found an lower refinement.
                 */
                Value<T1>* newlimit = new Value<T1>();
                typename std::vector< const Bound<T1, T2>* >::iterator bound = lPremise->begin();
                Iterator rowEntry = Iterator( basicVar.startEntry(), mpEntries );
                while( true )
                {
                    *newlimit += (*bound)->limit() * (*rowEntry).content();
                    ++bound;
                    if( !rowEntry.hEnd( false ) ) rowEntry.hMove( false );
                    else break;
                }
                /*
                 * Learn that the strongest weaker lower bound should be activated.
                 */
                const typename Bound<T1, T2>::BoundSet& lowerBounds = basicVar.lowerbounds();
                auto lbound = lowerBounds.rbegin();
                while( lbound != lowerBounds.rend() )
                {
                    #ifdef LRA_NO_DIVISION
                    if( **lbound < (*newlimit)/rowFactor && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced() )
                    #else
                    if( **lbound < *newlimit && (*lbound)->type() != Bound<T1, T2>::EQUAL && !(*lbound)->deduced() )
                    #endif
                    {
                        break;
                    }
                    if( *lbound == basicVar.pInfimum()  )
                    {
                        delete newlimit;
                        delete lPremise;
                        return;
                    }
                    ++lbound;
                }
                if( lbound != --lowerBounds.rend() )
                {
                    assert( ((*lbound)->type() != Bound<T1, T2>::EQUAL) );
                    LearnedBound learnedBound = LearnedBound();
                    learnedBound.nextWeakerBound = *lbound;
                    learnedBound.premise = std::vector<const Bound<T1, T2>*>( std::move( *lPremise ) );
                    delete lPremise;
                    #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                    #ifdef LRA_NO_DIVISION
                    if( newlimit->mainPart() > (*lbound)->limit().mainPart()*rowFactor || (*lbound)->limit().deltaPart() == 0 )
                    #else
                    if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                    #endif
                    {
                        #ifdef LRA_NO_DIVISION
                        smtrat::Polynomial lhs = (*lbound)->variable().expression()*(Rational)rowFactor - (Rational)newlimit->mainPart();
                        #else
                        smtrat::Polynomial lhs = (*lbound)->variable().expression() - (Rational)newlimit->mainPart();
                        #endif
                        smtrat::Relation rel = newlimit->deltaPart() != 0 ? smtrat::Relation::GREATER : smtrat::Relation::GEQ;
                        const smtrat::Constraint* constraint = smtrat::newConstraint( lhs, rel );
                        learnedBound.newBound = basicVar.addLowerBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                    }
                    else
                    {
                        learnedBound.newBound = NULL;
                    }
                    #else
                    delete newlimit;
                    learnedBound.newBound = NULL;
                    #endif
                    std::pair<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator, bool> insertionResult = mLearnedLowerBounds.insert( std::pair<Variable<T1, T2>*, LearnedBound>( _basicVar, learnedBound ) );
                    if( !insertionResult.second )
                    {
                        if( *learnedBound.nextWeakerBound > *insertionResult.first->second.nextWeakerBound )
                        {
                            insertionResult.first->second.nextWeakerBound = learnedBound.nextWeakerBound;
                            insertionResult.first->second.premise = learnedBound.premise;
                            mNewLearnedBounds.push_back( insertionResult.first );
                        }
                    }
                    else
                    {
                        mNewLearnedBounds.push_back( insertionResult.first );
                    }
                }
                else
                {
                    delete newlimit;
                    delete lPremise;
                }
            }
        }
        #endif
        
        /**
         * 
         * @param _var
         * @return 
         */
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::unboundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium ) const
        {
            if( _var.startEntry() == LAST_ENTRY_ID )
            {
                return 0;
            }
            else
            {
                size_t unboundedVars = 0;
                if( _var.isBasic() )
                {
                    Iterator rowEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (*rowEntry).columnVar()->infimum().isInfinite() || (*rowEntry).columnVar()->supremum().isInfinite() )
                        {
                            ++unboundedVars;
                            if( _stopCriterium != 0 && unboundedVars >= _stopCriterium )
                                return _stopCriterium + 1;
                        }
                        if( rowEntry.hEnd( false ) )
                            break;
                        rowEntry.hMove( false );
                    }
                }
                else
                {
                    Iterator columnEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( (*columnEntry).rowVar()->infimum().isInfinite() || (*columnEntry).rowVar()->supremum().isInfinite() )
                        {
                            ++unboundedVars;
                            if( _stopCriterium != 0 && unboundedVars >= _stopCriterium )
                                return _stopCriterium + 1;
                        }
                        if( columnEntry.vEnd( false ) )
                            break;
                        columnEntry.vMove( false );
                    }
                }
                return unboundedVars;
            }
        }
        
        /**
         * 
         * @param _var
         * @return 
         */
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::boundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium ) const
        {
            if( _var.startEntry() == LAST_ENTRY_ID )
            {
                return 0;
            }
            else
            {
                size_t boundedVars = 0;
                if( _var.isBasic() )
                {
                    Iterator rowEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( !(*rowEntry).columnVar()->infimum().isInfinite() || !(*rowEntry).columnVar()->supremum().isInfinite() )
                        {
                            ++boundedVars;
                            if( _stopCriterium != 0 && boundedVars >= _stopCriterium )
                                return _stopCriterium+1;
                        }
                        if( rowEntry.hEnd( false ) )
                            break;
                        rowEntry.hMove( false );
                    }
                }
                else
                {
                    Iterator columnEntry = Iterator( _var.startEntry(), mpEntries );
                    while( true )
                    {
                        if( !(*columnEntry).rowVar()->infimum().isInfinite() || !(*columnEntry).rowVar()->supremum().isInfinite() )
                        {
                            ++boundedVars;
                            if( _stopCriterium != 0 && boundedVars >= _stopCriterium )
                                return _stopCriterium+1;
                        }
                        if( columnEntry.vEnd( false ) )
                            break;
                        columnEntry.vMove( false );
                    }
                }
                return boundedVars;
            }
        }

        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::checkCorrectness() const
        {
            size_t rowNumber = 0;
            for( ; rowNumber < mRows.size(); ++rowNumber )
            {
                if( !rowCorrect( rowNumber ) ) return rowNumber;
            }
            return rowNumber;
        }

        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        bool Tableau<T1,T2>::rowCorrect( size_t _rowNumber ) const
        {
            if( mRows[_rowNumber] == NULL ) return false;
            if( _rowNumber != mRows[_rowNumber]->position() ) return false;
            size_t numOfRowElements = 0;
            smtrat::Polynomial sumOfNonbasics = smtrat::ZERO_POLYNOMIAL;
            Iterator rowEntry = Iterator( mRows[_rowNumber]->startEntry(), mpEntries );
            while( !rowEntry.hEnd( false ) )
            {
                sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
                ++numOfRowElements;
                rowEntry.hMove( false );
            }
            ++numOfRowElements;
            if( numOfRowElements != mRows[_rowNumber]->size() )
            {
                return false;
            }
            sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
            #ifdef LRA_NO_DIVISION
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::Polynomial( mRows[_rowNumber]->factor() ) * smtrat::MINUS_ONE_POLYNOMIAL;
            #else
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::MINUS_ONE_POLYNOMIAL;
            #endif
            if( !sumOfNonbasics.isZero() ) return false;
            return true;
        }
        
        #ifdef LRA_CUTS_FROM_PROOFS
        /**
         * Checks whether a constraint is a defining constraint. 
         * 
         * @return true,    if the constraint is a defining constraint
         *         false,   otherwise   
         */
        template<typename T1, typename T2>
        const smtrat::Constraint* Tableau<T1,T2>::isDefining( size_t row_index, T2& max_value ) const
        {
            const Variable<T1, T2>& basic_var = *mRows.at(row_index);
            basic_var.expression();
            bool upper_bound_hit = false;
            Iterator row_iterator = Iterator( basic_var.startEntry() , mpEntries );
            if( basic_var.infimum() == basic_var.assignment() || basic_var.supremum() == basic_var.assignment() )
            {
                if( basic_var.supremum() == basic_var.assignment() ) 
                {
                    upper_bound_hit = true;                    
                }
                /*
                 * The row represents a DC. Collect the nonbasics and the referring coefficients.
                 */
                Polynomial dc_poly = Polynomial();
                dc_poly = basic_var.expression();
                if( upper_bound_hit )
                {
                    dc_poly = dc_poly -  (Rational)(basic_var.supremum().limit().mainPart());
                }
                else
                {
                    dc_poly = dc_poly - (Rational)(basic_var.infimum().limit().mainPart());
                }
                std::cout << dc_poly << std::endl;
                const smtrat::Constraint* dc_constraint = newConstraint( dc_poly, Relation::EQ );
                std::cout << *dc_constraint << std::endl;
                return dc_constraint;
            }
            else
            {
                while( true )
                {
                    T2 abs_content = carl::abs((*row_iterator).content());
                    if(abs_content > max_value)
                    {
                        max_value = abs_content;                        
                    }
                    if( !row_iterator.hEnd( false ) )
                    {
                        row_iterator.hMove( false );
                    }
                    else
                    {
                        break;
                    }                    
                }                
            }
            return NULL;
        }
        
        /**
         * Checks whether the row with index row_index 
         * is defining. 
         * 
         * @return true,    if so
         *         false,   otherwise   
         */ 
        template<typename T1, typename T2>
        bool Tableau<T1,T2>::isDefining_Easy(std::vector<size_t>& dc_positions,size_t row_index)
        {
            auto vector_iterator = dc_positions.begin();
            while(vector_iterator != dc_positions.end())
            {
                if(*vector_iterator == row_index)
                {
                    return true;
                }
            }
            return false;
        }
        
        /**
         * Checks whether the column with index column_index 
         * is a diagonal column. 
         * 
         * @return true,    if the column with index column_index is a diagonal column
         *         false,   otherwise   
         */        
        template<typename T1, typename T2>
        bool Tableau<T1,T2>::isDiagonal(size_t column_index , std::vector<size_t>& diagonals)
        {
        size_t i=0;
        while(diagonals.at(i) != mColumns.size())
        {
            if(diagonals.at(i) == column_index)
            {
                return true;
            }
        ++i;    
        }
        return false;            
        }
        
        /**
         * Returns the row of the defining constraint with index row_index
         * in the Tableau containing this DC.
         * 
         */ 
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::position_DC(size_t row_index,std::vector<size_t>& dc_positions)
        {
            auto vector_iterator = dc_positions.begin();
            size_t i=0;
            while(vector_iterator != dc_positions.end())
            {
                if(*vector_iterator == row_index)
                {
                    return i;
                }
                ++i;
                ++vector_iterator;
            }
            return mRows.size();
        }
        
        /**
         * Returns the the actual index of the column with
         * index column_index in the permutated tableau.   
         */        
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::revert_diagonals(size_t column_index,std::vector<size_t>& diagonals)
        {
            size_t i=0;
            while(diagonals.at(i) != mColumns.size())   
            {
                if(diagonals.at(i) == column_index)
                {
                    return i;
                }
                ++i;
            }
            return mColumns.size();
        }
        
        /**
         * Multiplies all entries in the column with the index column_index by (-1). 
         * 
         * @return   
         */        
        template<typename T1, typename T2>
        void Tableau<T1,T2>::invertColumn(size_t column_index)
        {   
            Iterator column_iterator = Iterator( (*mColumns.at(column_index)).startEntry(), mpEntries );   
            while(true)
            {
                (*mpEntries)[column_iterator.entryID()].rContent() = (-1)*(((*mpEntries)[column_iterator.entryID()].rContent()).content());
                if(!column_iterator.vEnd( false ))
                {
                    column_iterator.vMove( false );            
                } 
                else 
                {
                    break;
                }
            }        
        }
        
        /**
         * Adds the column with index columnB_index multplied by multiple 
         * to the column with index columnA_index.
         * 
         * @return 
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::addColumns( size_t columnA_index, size_t columnB_index, T2 multiple)
        {
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            std::cout << __func__ << "( " << columnA_index << ", " << columnB_index << ", " << multiple << " )" << std::endl;
            #endif
            Iterator columnA_iterator = Iterator((*mColumns.at(columnA_index)).startEntry(), mpEntries);
            Iterator columnB_iterator = Iterator((*mColumns.at(columnB_index)).startEntry(), mpEntries);
                
            while(true)
            {
            /* 
             * Make columnA_iterator and columnB_iterator neighbors. 
             */ 
            while( (*(*columnA_iterator).rowVar()).position() > (*(*columnB_iterator).rowVar()).position() && !columnA_iterator.vEnd( false ) )
            {
                columnA_iterator.vMove( false );
            }    
            EntryID ID1_to_be_Fixed,ID2_to_be_Fixed;            
            if( (*(*columnA_iterator).rowVar()).position() == (*(*columnB_iterator).rowVar()).position() )
            {
                T2 content = T2(((*columnA_iterator).content().content())+((multiple.content())*((*columnB_iterator).content().content())));  
                if(content == 0)
                {
                    EntryID to_delete = columnA_iterator.entryID();
                    if(!columnA_iterator.vEnd( false ))
                    {                        
                        columnA_iterator.vMove( false );
                    }    
                    removeEntry(to_delete);                
                 }                
                 else
                 {
                    (*columnA_iterator).rContent() = content;           
                 }    
              }
              else if( (*(*columnA_iterator).rowVar()).position() < (*(*columnB_iterator).rowVar()).position() ) 
              {
                  /*
                   * A new entry has to be created under the position of columnA_iterator
                   * and sideways to column_B_iterator.
                   */   
                  EntryID entryID = newTableauEntry(T2(((multiple.content())*((*columnB_iterator).content().content()))));
                  TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                  TableauEntry<T1,T2>& entry_down = (*mpEntries)[(*columnA_iterator).vNext( true )];   
                  EntryID down = (*columnA_iterator).vNext( true );
                  entry.setColumnVar( (*columnA_iterator).columnVar() );
                  entry.setRowVar( (*columnB_iterator).rowVar() );
                  entry.setVNext( true, down);
                  entry.setVNext( false,columnA_iterator.entryID());
                  entry_down.setVNext( false,entryID);
                  (*columnA_iterator).setVNext( true, entryID);
                  Variable<T1, T2>& nonBasicVar = *mColumns[(*entry.columnVar()).position()];
                  ++nonBasicVar.rSize();
                  //TableauHead& columnHead = mColumns[entry.columnNumber()];
                  //++columnHead.mSize;
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() )
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */
                      while( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && !row_iterator.hEnd( true ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( true ); 
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && row_iterator.hEnd( true ) )
                      {                          
                          (*mpEntries)[entryID].setHNext( true,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          mRows[(*(*columnB_iterator).rowVar()).position()]->rStartEntry() = entryID;
                          //TableauHead& rowHead = mRows[(*columnB_iterator).rowNumber()];
                          //rowHead.mStartEntry = entryID;
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( false,ID1_to_be_Fixed);
                      }
                  }    
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && !row_iterator.hEnd( false ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( false );
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && row_iterator.hEnd( false ) )
                      {
                          (*mpEntries)[entryID].setHNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( true,ID1_to_be_Fixed);
                      }
                  }
                  ++(mRows[(*entry.rowVar()).position()]->rSize());
                  //TableauHead& rowHead = mRows[entry.rowNumber()];
                  //++rowHead.mSize;                      
                  //if(columnHead.mStartEntry == columnA_iterator.entryID())
                  if( nonBasicVar.startEntry() == columnA_iterator.entryID() )    
                  {
                      nonBasicVar.rStartEntry() = entryID;
                      //columnHead.mStartEntry = entryID;
                  }  
                                   
              }
              else
              {
                  /*
                   * A new entry has to be created above the position of columnA_iterator
                   * and sideways to column_B_iterator.
                   */                   
                  EntryID entryID = newTableauEntry(T2(((multiple.content())*((*columnB_iterator).content().content()))));
                  TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                  entry.setColumnVar((*columnA_iterator).columnVar());
                  entry.setRowVar((*columnB_iterator).rowVar());
                  entry.setVNext( true,columnA_iterator.entryID());
                  entry.setVNext( false,LAST_ENTRY_ID);
                  (*columnA_iterator).setVNext( false,entryID);
                  Variable<T1, T2>& nonBasicVar = *mColumns[(*entry.columnVar()).position()];
                  ++nonBasicVar.rSize();                  
                  //TableauHead& columnHead = mColumns[entry.columnNumber()];
                  //++columnHead.mSize;
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() )
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && !row_iterator.hEnd( true ) )
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( true );                     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() > entry.columnVar()->position() && row_iterator.hEnd( true ) )
                      {
                          (*mpEntries)[entryID].setHNext( true,LAST_ENTRY_ID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          mRows[(*(*columnB_iterator).rowVar()).position()]->rStartEntry() = entryID;
                          //TableauHead& rowHead = mRows[(*columnB_iterator).rowNumber()];
                          //rowHead.mStartEntry = entryID;                          
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( false,ID1_to_be_Fixed);
                      }  
                  }  
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && !row_iterator.hEnd( false ) )
                      {                             
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hMove( false );     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if( (*(*row_iterator).columnVar()).position() < entry.columnVar()->position() && row_iterator.hEnd( false ) )
                      {
                          (*mpEntries)[entryID].setHNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHNext( false,entryID);
                          (*mpEntries)[entryID].setHNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHNext( true,ID1_to_be_Fixed);
                      }                      
                  }
               ++mRows[(*(entry.rowVar())).position()]->rSize();   
               //TableauHead& rowHead = mRows[entry.rowNumber()];
               //++rowHead.mSize;                  
               }
               if(!columnB_iterator.vEnd( false ))
               {
                   columnB_iterator.vMove( false );
               }
               else
               { 
                   break;
               }    
           }
        }
        
        /**
         * Multiplies the row with index row_index by multiple.
         * 
         * @return 
         */        
        template<typename T1, typename T2> 
        void Tableau<T1,T2>::multiplyRow(size_t row_index,T2 multiple)
        {            
            const Variable<T1, T2>& basic_var = *mRows.at(row_index);
            Iterator row_iterator = Iterator( basic_var.position(), mpEntries);
            while(true)
            { 
                T2 content = T2(((*row_iterator).content().content())*(multiple.content()));
                (*row_iterator).rContent() = content;
                if(!row_iterator.hEnd( false ))
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    break;
                }
            }
        }
        
        /**
         * Calculates the scalarproduct of the row with index rowA from Tableau A with the column
         * with index columnB from Tableau B considering that the columns in B are permutated. 
         * 
         * @return   the value (T) of the scalarproduct.
         */        
        template<typename T1, typename T2> 
        std::pair< const Variable<T1,T2>*, T2 > Tableau<T1,T2>::Scalar_Product(Tableau<T1,T2>& A, Tableau<T1,T2>& B,size_t rowA, size_t columnB,std::vector<size_t>& diagonals,std::vector<size_t>& dc_positions) 
        {
            //A.print( LAST_ENTRY_ID, std::cout, "", true, true );
            //B.print( LAST_ENTRY_ID, std::cout, "", true, true );
            //for( auto iter = diagonals.begin(); iter != diagonals.end(); ++iter ) 
                //printf( "%u", *iter ); 
            Iterator rowA_iterator = Iterator((*A.mRows.at(rowA)).startEntry(),A.mpEntries);
            Iterator columnB_iterator = Iterator( (*B.mColumns.at(columnB)).startEntry(),B.mpEntries );
            T2 sum = T2(0);
            while(true)
            {
                columnB_iterator = Iterator( (*B.mColumns.at(columnB)).startEntry(),B.mpEntries );
                size_t actual_column = revert_diagonals( (*(*rowA_iterator).columnVar()).position(),diagonals ); 
                while(true)
                {
                    if( actual_column == position_DC( (*(*columnB_iterator).rowVar()).position(),dc_positions) )
                    {
                        sum += (*rowA_iterator).content()*(*columnB_iterator).content();
                        break;
                    }
                    if(columnB_iterator.vEnd( false ))
                    {
                        break;
                    }
                    else
                    {
                        columnB_iterator.vMove( false );
                    }
                }
                if(rowA_iterator.hEnd( false ))
                {
                    break;
                }
                else
                {
                    rowA_iterator.hMove( false );
                }  
            }    
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            std::cout << sum << std::endl;
            #endif
            std::pair< const Variable<T1,T2>*, T2 > result = std::pair< const Variable<T1,T2>*, T2 >((*columnB_iterator).columnVar(),sum);
            return result;    
        }
        
        /**
         * Calculate the Hermite normal form of the calling Tableau. 
         * 
         * @return   the vector containing the indices of the diagonal elements.
         */        
        template<typename T1, typename T2> 
        void Tableau<T1,T2>::calculate_hermite_normalform(std::vector<size_t>& diagonals)
        {
            for(size_t i=0;i<mColumns.size();i++)
            {
                diagonals.push_back(mColumns.size());
            }  
            Iterator row_iterator = Iterator( (*mRows.at(0)).startEntry(), mpEntries);          
            bool first_free;
            bool first_loop;
            bool just_deleted; 
            /*
             * Iterate through all rows in order to construct the HNF.
             */
            for(size_t i=0;i<mRows.size();++i)
            {
                size_t elim_pos=mColumns.size(),added_pos=mColumns.size();
                EntryID added_entry,elim_entry;
                T2 elim_content, added_content;     
                row_iterator = Iterator( (*mRows.at(i)).startEntry(), mpEntries);
                size_t number_of_entries = (*mRows.at(i)).size();
                first_loop = true;
                first_free = true;
                just_deleted = false;
                /*
                 * Count how many zero entries of diagonal columns are in the
                 * current row.
                 */
                size_t diag_zero_entries=0;
                for(size_t j=0;j<i;j++)
                {
                    Iterator diagonal_iterator = Iterator( (*mColumns.at(diagonals.at(j))).startEntry(), mpEntries);
                    while( (*diagonal_iterator).rowVar()->position() > i && !diagonal_iterator.vEnd( false ) )
                    {
                        diagonal_iterator.vMove( false );
                    }
                    if( (*diagonal_iterator).rowVar()->position() != i )
                    {
                        diag_zero_entries++;
                    }
                }             
                /*
                 * Eliminate as many entries as necessary.
                 */
                while(number_of_entries + diag_zero_entries > i + 1)
                {
                    if(just_deleted)
                    {
                        /*
                         * Move the iterator to the correct position if an entry
                         * has been deleted in the last loop run.
                         */
                        row_iterator = Iterator(added_entry, mpEntries);
                    }    
                    else if (!first_loop)
                    {
                        /*
                         * If no entry was deleted during the last loop run and it is not 
                         * the first loop run, correct the position of the iterators.
                         */                        
                        if((*(*mpEntries)[added_entry].columnVar()).position() > (*(*mpEntries)[elim_entry].columnVar()).position())
                        {
                            row_iterator = Iterator(elim_entry,mpEntries);
                        }    
                        else
                        {
                            row_iterator = Iterator(added_entry,mpEntries);
                        }    
                    }
                    /*
                     * Make all entries in the current row positive.
                     */
                    Iterator help_iterator = Iterator((*mRows.at(i)).startEntry(), mpEntries);
                    while(true)
                    {
                        if((*help_iterator).content() < 0 && !isDiagonal((*(*help_iterator).columnVar()).position(),diagonals))
                        {
                            invertColumn((*(*help_iterator).columnVar()).position());
                        }
                        if(!help_iterator.hEnd( false ))
                        {
                            help_iterator.hMove( false );
                        }
                        else
                        {
                            break;
                        }
                    }
                    
                    while(elim_pos == added_pos)
                    {
                        T2 content = (*mpEntries)[row_iterator.entryID()].content();
                        size_t column = (*(*mpEntries)[row_iterator.entryID()].columnVar()).position();   
                        if(!isDiagonal(column,diagonals))
                        {    
                            if(first_free)
                            {                                
                                elim_pos = column;
                                elim_content = content; 
                                added_pos = column;
                                added_content = content;
                                first_free = false;
                                added_entry = row_iterator.entryID();
                                elim_entry = row_iterator.entryID();
                            }
                            else
                            {
                                if(elim_content <= content)
                                {
                                    elim_pos = column;
                                    elim_content = content;  
                                    elim_entry = row_iterator.entryID();
                                }
                                else
                                {
                                    added_pos = column;
                                    added_content = content; 
                                    added_entry = row_iterator.entryID();
                                }
                             }
                        }                        
                        if(elim_pos == added_pos && !row_iterator.hEnd( false ))
                        {
                            row_iterator.hMove( false );  
                        }    
                    }
                    T2 floor_value = T2( (carl::floor( (Rational)(elim_content / added_content) ) ) );
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "floor_value = " << floor_value << std::endl;
                    std::cout << "added_content = " << added_content << std::endl;
                    std::cout << "elim_content = " << elim_content << std::endl;
                    std::cout << "T2((-1)*floor_value.content()*added_content.content()) = " << T2((-1)*floor_value.content()*added_content.content()) << std::endl;
                    #endif
                    addColumns(elim_pos,added_pos,T2((-1)*floor_value.content()));
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "Add " << (added_pos+1) << ". column to " << (elim_pos+1) << ". column:" << std::endl;
                    print( LAST_ENTRY_ID, std::cout, "", true, true );
                    #endif
                    number_of_entries = (*mRows.at(i)).size(); 
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "Number of entries: " << number_of_entries << std::endl;
                    std::cout << "Zero entries: " << diag_zero_entries << std::endl;
                    std::cout << "i: " << i << std::endl;
                    #endif
                    first_loop = false;
                    if(mod( (Rational)elim_content, (Rational)added_content ) == 0)
                    {
                        /*
                         * If the remain of the division is zero,
                         * the following addition will delete
                         * the entry with the ID elim_entry
                         */
                        just_deleted = true; 
                        first_free = true;
                        elim_pos = added_pos;
                        elim_entry = added_entry;
                    }    
                    else
                    {
                         just_deleted = false;  
                         first_free = true;
                         if(elim_pos < added_pos)
                         {
                             added_pos = elim_pos;
                         }    
                         else
                         {
                             elim_pos = added_pos;
                         }         
                    }
                }
                if(first_loop)
                {
                    /*
                     * The current row does not need any eliminations.
                     * So search manually for the diagonal element.
                     */
                    while(isDiagonal((*(*row_iterator).columnVar()).position(),diagonals))
                    {
                        row_iterator.hMove( false );                        
                    }
                    if( (*row_iterator).content() < 0 )
                    {
                        invertColumn( (*(*row_iterator).columnVar()).position() );
                    }
                    added_content = (*row_iterator).content();
                    added_pos = (*(*row_iterator).columnVar()).position();
                } 
                diagonals.at(i) = added_pos;                
                /*
                 *  Normalize row.
                 */
                row_iterator = Iterator((*mRows.at(i)).startEntry(), mpEntries);
                while(true)
                {   
                    if( (*(*row_iterator).columnVar()).position() != added_pos && isDiagonal((*(*row_iterator).columnVar()).position(),diagonals) && ( added_content <= carl::abs( (*row_iterator).content() ) || (*row_iterator).content() > 0 ) )
                    {
                       /*
                        * The current entry has to be normalized because it´s
                        * in a diagonal column and greater or equal than the
                        * diagonal entry in the current row.
                        */
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        std::cout << "Normalize" << std::endl;
                        std::cout << (*(*mpEntries)[row_iterator.entryID()].columnVar()).position() << std::endl;
                        std::cout << diagonals.at(i) << std::endl;
                        #endif
                        T2 floor_value = T2( (carl::floor( (Rational)(carl::abs( (*row_iterator).content() / added_content) ) ) ) );
                        if( carl::mod( carl::abs( (*row_iterator).content() ) , added_content ) != 0 )
                        {
                            ++floor_value;
                        }
                        T2 inverter = (Rational)1;
                        if ( (*row_iterator).content() < 0 )
                        {
                            inverter = inverter * (Rational)-1;                            
                        }
                        addColumns((*(*mpEntries)[row_iterator.entryID()].columnVar()).position(),
                                  diagonals.at(i),
                                  (Rational)(-1)*inverter*(Rational)(floor_value));
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        print();
                        #endif
                    }
                    if(!row_iterator.hEnd( false ))
                    {
                        row_iterator.hMove( false ); 
                    }
                    else
                    {
                        break;
                    }
                }                
            }  
        }     
        
        /*
         * Inverts the HNF matrix.
         * 
         * @return 
         */
        template<typename T1, typename T2> 
        void Tableau<T1,T2>::invert_HNF_Matrix(std::vector<size_t>& diagonals)
        {
            /*
             * Iterate through the tableau beginning in the the last
             * column which only contains one element.
             */  
            size_t i = mRows.size()-1;
            std::map< std::pair<size_t, size_t >, T2 > changed_values  = std::map< std::pair<size_t, size_t>, T2 >();
            while( true )
            {
                /*
                 * Move the iterator to the diagonal element in the current column
                 * and calculate the new content for it.
                 */
                Iterator column_iterator = Iterator( (*mColumns.at(diagonals.at(i))).startEntry(), mpEntries ); 
                while( !column_iterator.vEnd( false ) )
                {
                    column_iterator.vMove( false );                  
                } 
                changed_values[std::pair<size_t, size_t >((*column_iterator).rowVar()->position(), (*column_iterator).rowVar()->position()  )] = (*column_iterator).content();
                (*column_iterator).rContent() = 1/(*column_iterator).content();
                /*
                 * Now change the other entries in the current column if necessary.
                 */
                if(column_iterator.vEnd( true ))
                {
                    if(i == 0)
                    {
                        return;
                    }
                    --i;
                    continue;
                }
                column_iterator.vMove( true );
                Iterator row_iterator = Iterator( (*column_iterator).rowVar()->startEntry(), mpEntries );
                while( true )
                {
                    size_t res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                    while( res < (*(*column_iterator).rowVar()).position() && !row_iterator.hEnd( false ) )
                    {
                        row_iterator.hMove( false );
                        res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                    }
                    if( res == (*(*column_iterator).rowVar()).position() )
                    {
                        changed_values[std::pair<size_t, size_t >((*column_iterator).rowVar()->position(), revert_diagonals( (*column_iterator).columnVar()->position(), diagonals ) )] = (*column_iterator).content();
                        T2& value_to_be_changed = (*column_iterator).rContent();
                        T2 divisor = changed_values.at(std::pair<size_t, size_t >((*row_iterator).rowVar()->position(), res ));  
                        T2 sum = 0; 
                        Iterator column_iterator2 = Iterator( column_iterator.entryID(), mpEntries );
                        row_iterator = Iterator( (*column_iterator2).rowVar()->startEntry(), mpEntries );
                        column_iterator2.vMove( false );
                        while( true )
                        {
                            res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                            while( res != (*(*column_iterator2).rowVar()).position() && !row_iterator.hEnd( false ) )
                            {
                                row_iterator.hMove( false );
                                res = revert_diagonals( (*(*row_iterator).columnVar()).position(), diagonals );
                            }
                            if( res == (*(*column_iterator2).rowVar()).position() )
                            {
                                sum = sum-(*row_iterator).content()*(*column_iterator2).content();
                            }                             
                            if( column_iterator2.vEnd( false ) )
                            {
                                break;
                            }
                            column_iterator2.vMove( false );
                        }   
                        value_to_be_changed = sum / divisor;
                    }  
                    if(!column_iterator.vEnd( true ))
                    {
                        column_iterator.vMove( true );
                    }
                    else
                    {
                        break;
                    }
                }    
                if(i == 0)
                {
                    return;
                }
                --i;
            }
        }
        
        /**
         * Checks whether a cut from proof can be constructed with the row with index row_index
         * in the DC_Tableau. 
         * 
         * @return the valid proof,    if the proof can be constructed.
         *         NULL,               otherwise.   
         */
        template<typename T1, typename T2>
        smtrat::Polynomial* Tableau<T1,T2>::create_cut_from_proof(Tableau<T1,T2>& Inverted_Tableau, Tableau<T1,T2>& DC_Tableau, size_t row_index, std::vector<size_t>& diagonals, std::vector<size_t>& dc_positions, T2& lower, T2& max_value)
        {
            Value<T1> result = T2(0);
            assert( mRows.size() > row_index );
            Iterator row_iterator = Iterator( (*mRows.at(row_index)).startEntry(),mpEntries); 
            /*
             * Calculate H^(-1)*b 
             */
            size_t i;
            while(true)
            {
                i = revert_diagonals((*(*row_iterator).columnVar()).position(),diagonals);
                assert( i < mColumns.size() );
                const Variable<T1, T2>& basic_var = *(DC_Tableau.mRows).at(dc_positions.at(i));
                result += basic_var.assignment() * (*row_iterator).content();                    
                if(row_iterator.hEnd( false ))
                {
                    break;
                }
                else
                {
                    row_iterator.hMove( false );
                }                
            }
            std::cout << "Result: " << result.mainPart() << std::endl;
            if( !carl::isInteger( (Rational)result.mainPart() ) )
            {
                std::cout << "Fractional result: " << result.mainPart() << std::endl;
                // Construct the Cut
                std::pair< const Variable<T1,T2>*, T2 > product;
                size_t i=0;
                Polynomial* sum = new Polynomial();
                T2 gcd_row = T2(1);
                while(i < DC_Tableau.mColumns.size())
                {
                    // Check whether the current column variable also exists in the inverted Tableau
                    size_t j = 0;
                    bool var_exists = false;
                    const Variable<T1, T2>* nonBasicVar = DC_Tableau.mColumns.at(i);
                    while( j < Inverted_Tableau.mColumns.size() && !var_exists )
                    {
                        if( (*nonBasicVar).expression() ==  (*Inverted_Tableau.columns().at(j)).expression() )
                        {
                            var_exists = true;
                        }
                        ++j;
                    }
                    if( var_exists )
                    {
                        std::cout << "Scalar_product with row: " << row_index << std::endl;
                        std::cout << "Scalar_product with column: " << i << std::endl;
                        //std::cout << "Row: " << Inverted_Tableau.mRows.at(i)->expression() << std::endl;
                        product = Scalar_Product(Inverted_Tableau,DC_Tableau,row_index,i,diagonals,dc_positions);
                    }
                    else
                    {
                        std::cout << "Var not included: " << i << std::endl;
                        product.second = 0;
                    }
                    if(product.second != 0)
                    {
                        std::cout << "Coefficient: " << product.second << std::endl;
                        T2 temp = (Rational)(carl::getDenom((Rational)result.mainPart()))*(Rational)product.second;
                        std::cout << "Coefficient*Denom: " << temp << std::endl;
                        gcd_row  = carl::gcd( gcd_row , temp );
                        *sum += (*product.first).expression()*(Rational)temp;
                    }
                    ++i;
                }
                /* Check whether the proof of unsatisfiability contains a coefficient which is greater 
                 * than max_value*gcd_row and also divide the coefficients of the sum by gcd_row 
                 * according to the algorithm.
                 */ 
                std::cout << "Cut: " << *sum << std::endl;
                auto iter = (*sum).begin();
                while( iter != (*sum).end() )
                {
                    if( (*(*iter)).coeff() > max_value*gcd_row )
                    {
                        return NULL;                        
                    }
                    (*(*iter)).divideBy((Rational)gcd_row);
                    ++iter;
                }
                lower = (Rational)carl::getNum((Rational)result.mainPart())/(Rational)gcd_row;
                std::cout << "Numerator: " << carl::getNum((Rational)result.mainPart()) << std::endl;
                std::cout << "Denominator: " << carl::getDenom((Rational)result.mainPart()) << std::endl;
                std::cout << "gcd: " << gcd_row << std::endl;
                std::cout << "lower: " << lower << std::endl;
                std::cout << "Cut: " << *sum << std::endl;
                return sum; 
            }
            else
            {                
                return NULL;                
            }
        }
        #endif
        
        #ifdef LRA_GOMORY_CUTS
        enum GOMORY_SET
        {
            J_PLUS,
            J_MINUS,
            K_PLUS,
            K_MINUS
        };

        /**
         * Creates a constraint referring to Gomory Cuts, if possible. 
         * 
         * @return NULL,    if the cut can´t be constructed;
         *         otherwise the valid constraint is returned.   
         */ 
        template<typename T1, typename T2>
        const smtrat::Constraint* Tableau<T1,T2>::gomoryCut( const T2& _ass, Variable<T1,T2>* _rowVar, std::vector<const smtrat::Constraint*>& _constrVec )
        { 
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            std::vector<GOMORY_SET> splitting = std::vector<GOMORY_SET>();
            // Check, whether the premises for a Gomory Cut are satisfied
            while( !row_iterator.hEnd( false ) )
            { 
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();
                if( nonBasicVar.infimum() == nonBasicVar.assignment() || nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    if( nonBasicVar.infimum() == nonBasicVar.assignment() )
                    {
                        if( (*row_iterator).content() < 0 ) 
                        {
                            splitting.push_back( J_MINUS );
                        }    
                        else 
                        {
                            splitting.push_back( J_PLUS );    
                        }
                    }
                    else
                    {
                        if( (*row_iterator).content() < 0 ) 
                        {
                            splitting.push_back( K_MINUS );
                        }    
                        else 
                        {
                            splitting.push_back( K_PLUS );
                        }
                    }
                }                                 
                else
                {
                    std::cout << "Not able to construct" << std::endl;
                    return NULL;
                }      
                row_iterator.hMove( false );
            }
            // A Gomory Cut can be constructed
            std::cout << "Create Cut for: " << _rowVar->expression() << std::endl;
            T2 coeff;
            T2 f_zero = _ass - T2(carl::floor( (Rational)_ass ));
            Polynomial sum = Polynomial();
            // Construction of the Gomory Cut 
            std::vector<GOMORY_SET>::const_iterator vec_iter = splitting.begin();
            row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            while( !row_iterator.hEnd( false ) )
            {                 
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();  
                if( (*vec_iter) == J_MINUS )
                {
                    assert( nonBasicVar.infimum() == nonBasicVar.assignment() && (*row_iterator).content() < 0 );
                    T2 bound = nonBasicVar.infimum().limit().mainPart();
                    coeff = -( (*row_iterator).content() / f_zero);
                    _constrVec.push_back( nonBasicVar.infimum().pAsConstraint() );
                    sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)bound );                   
                }                 
                else if( (*vec_iter) == J_PLUS )
                {
                    assert( nonBasicVar.infimum() == nonBasicVar.assignment() && (*row_iterator).content() >= 0 );
                    T2 bound = nonBasicVar.infimum().limit().mainPart();
                    coeff = (*row_iterator).content()/( (Rational)1 - f_zero );
                    _constrVec.push_back( nonBasicVar.infimum().pAsConstraint() );
                    sum += (Rational)coeff*( nonBasicVar.expression() - (Rational)bound );                   
                }
                else if( (*vec_iter) == K_MINUS )
                {
                    assert( nonBasicVar.supremum() == nonBasicVar.assignment() && (*row_iterator).content() < 0 );
                    T2 bound = nonBasicVar.supremum().limit().mainPart();
                    coeff = -( (*row_iterator).content()/( (Rational)1 - f_zero ) );
                    _constrVec.push_back( nonBasicVar.supremum().pAsConstraint() );
                    sum += (Rational)coeff * ( (Rational)bound - nonBasicVar.expression() );                   
                }
                else if( (*vec_iter) == K_PLUS ) 
                {
                    assert( nonBasicVar.supremum() == nonBasicVar.assignment() && (*row_iterator).content() >= 0 );
                    T2 bound = nonBasicVar.supremum().limit().mainPart();
                    coeff = (*row_iterator).content()/f_zero;
                    _constrVec.push_back( nonBasicVar.supremum().pAsConstraint() );
                    sum += (Rational)coeff * ( (Rational)bound - nonBasicVar.expression() );
                }
                row_iterator.hMove( false );
                ++vec_iter;
            }
            sum = sum - (Rational)1;
            const smtrat::Constraint* gomory_constr = newConstraint( sum , Relation::GEQ );
            std::cout << *gomory_constr << std::endl;
            newBound(gomory_constr);
            // TODO: check whether there is already a basic variable with this polynomial (psum, cf. LRAModule::initialize(..)) 
            return gomory_constr;
        }
        #endif

        /**
         * @return number of entries in the row belonging to _rowVar  
         */ 
        template<typename T1, typename T2>
        size_t Tableau<T1,T2>::getNumberOfEntries(Variable<T1,T2>* _rowVar)
        {
            size_t result = 0;
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );
            while( true )
            {
                ++result;
                if( row_iterator.hEnd( false ) )
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    return result;
                }
            }
        }
        
        
        /**
         * Collects the premises for branch and bound and stores them in premises.  
         */ 
        template<typename T1, typename T2>
        void Tableau<T1,T2>::collect_premises(Variable<T1,T2>* _rowVar, PointerSet<Formula>& premises)
        {
            Iterator row_iterator = Iterator( _rowVar->startEntry(), mpEntries );  
            while( true )
            {
                const Variable<T1, T2>& nonBasicVar = *(*row_iterator).columnVar();
                if( nonBasicVar.infimum() == nonBasicVar.assignment() || nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    if( nonBasicVar.infimum() == nonBasicVar.assignment() )
                    {
                        premises.insert( newFormula( (*(*row_iterator).columnVar()).infimum().pAsConstraint() ) );                        
                    }
                    else
                    {
                        premises.insert( newFormula( (*(*row_iterator).columnVar()).supremum().pAsConstraint() ) );                        
                    }
                }
                if( row_iterator.hEnd( false ) )
                {
                    row_iterator.hMove( false );
                }
                else
                {
                    return;
                }              
            }            
        }

        /**
         *
         * @param _out
         * @param _maxEntryLength
         * @param _init
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::printHeap( std::ostream& _out, int _maxEntryLength, const std::string _init ) const
        {
            for( EntryID pos = 1; pos < mpEntries->size(); ++pos )
            {
                std::cout << _init;
                printEntry( pos, _out, _maxEntryLength );
                _out << std::endl;
            }
        }

        /**
         *
         * @param _out
         * @param _entry
         * @param _maxEntryLength
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::printEntry( EntryID _entry, std::ostream& _out, int _maxEntryLength ) const
        {
            _out << std::setw( 4 ) << _entry << ": ";
            std::stringstream out;
            if( _entry != LAST_ENTRY_ID )
            {
                out << (*mpEntries)[_entry].content();
                _out << std::setw( _maxEntryLength ) << out.str();
            }
            else
            {
                _out << std::setw( _maxEntryLength ) << "NULL";
            }
            _out << " at (";
            _out << std::setw( 4 ) << ((_entry == 0 || (*mpEntries)[_entry].rowVar() == NULL) ? 0 : (*mpEntries)[_entry].rowVar()->position());
            _out << ",";
            _out << std::setw( 4 ) << (_entry == 0 ? 0 : (*mpEntries)[_entry].columnVar()->position());
            _out << ") [up:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].vNext( false );
            _out << ", down:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].vNext( true );
            _out << ", left:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].hNext( true );
            _out << ", right:";
            _out << std::setw( 4 ) << (*mpEntries)[_entry].hNext( false );
            _out << "]";
            if( _entry != 0 && (*mpEntries)[_entry].rowVar() != NULL )
            {
                _out << " (" << *(*mpEntries)[_entry].rowVar()->pExpression() << ", " << *(*mpEntries)[_entry].columnVar()->pExpression() << ")"; 
            }
        }

        /**
         *
         * @param _out
         * @param _init
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::printVariables( bool _allBounds, std::ostream& _out, const std::string _init ) const
        {
            _out << _init << "Basic variables:" << std::endl;
            for( Variable<T1,T2>* rowVar : mRows )
            {
                if( rowVar != NULL )
                {
                    _out << _init << "  ";
                    rowVar->print( _out );
                    _out << "(" << unboundedVariables( *rowVar ) << ")" << std::endl;
                    if( _allBounds ) rowVar->printAllBounds( _out, _init + "                    " );
                }
            }
            _out << _init << "Nonbasic variables:" << std::endl;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                _out << _init << "  ";
                columnVar->print( _out );
                _out << "(" << unboundedVariables( *columnVar ) << ")" << std::endl;
                if( _allBounds ) columnVar->printAllBounds( _out, _init + "                    " );
            }
        }

        #ifdef LRA_REFINEMENT
        /**
         *
         * @param _out
         * @param _init
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::printLearnedBounds( const std::string _init, std::ostream& _out  ) const
        {
            for( auto learnedBound = mLearnedLowerBounds.begin(); learnedBound != mLearnedLowerBounds.end(); ++learnedBound )
            {
                printLearnedBound( *learnedBound->first, learnedBound->second, _init, _out );
            }
            for( auto learnedBound = mLearnedUpperBounds.begin(); learnedBound != mLearnedUpperBounds.end(); ++learnedBound )
            {
                printLearnedBound( *learnedBound->first, learnedBound->second, _init, _out );
            }
        }
        
        template<typename T1, typename T2>
        void Tableau<T1,T2>::printLearnedBound( const Variable<T1,T2>& _var, const LearnedBound& _learnedBound, const std::string _init, std::ostream& _out  ) const
        {
            for( auto premiseBound = _learnedBound.premise->begin(); premiseBound != _learnedBound.premise->end(); ++premiseBound )
            {
                _out << _init;
                _out << *(*premiseBound)->variable().pExpression();
                (*premiseBound)->print( true, _out, true );
                _out << std::endl;
            }
            _out << _init << "               | " << std::endl;
            _out << _init << "               V " << std::endl;
            _out << _init << *_var.pExpression();
            _learnedBound.nextWeakerBound->print( true, _out, true );
            _out << std::endl;
            _out << std::endl;
            #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
            _out << _init << *_var.pExpression();
            _learnedBound.newBound->print( true, _out, true );
            _out << std::endl << std::endl;
            #endif
        }
        #endif

        /**
         *
         * @param _out
         * @param _init
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::print( EntryID _pivotingElement, std::ostream& _out, const std::string _init, bool _friendlyNames, bool _withZeroColumns ) const
        {
            char frameSign = '-';
            char separator = '|';
            char pivoting_separator = '#';
            size_t pivotingRow = 0;
            size_t pivotingColumn = 0;
            size_t basic_var_assign_width = 1;
            size_t basic_var_infimum_width = 1;
            size_t basic_var_supremum_width = 1;
            size_t basic_var_name_width = 1;
            std::vector<size_t> columnWidths;
            // Set the widths.
            for( Variable<T1,T2>* rowVar : mRows )
            {
                if( rowVar != NULL )
                {
                    std::stringstream outA;
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        outA << rowVar->factor();
                    #endif
                    outA << rowVar->expression().toString( true, _friendlyNames );
                    size_t rowVarNameSize = outA.str().size();
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        rowVarNameSize += 5;
                    #endif
                    if( rowVarNameSize > basic_var_name_width )
                        basic_var_name_width = rowVarNameSize;
                    if( rowVar->assignment().toString().size() > basic_var_assign_width )
                        basic_var_assign_width = rowVar->assignment().toString().size();
                    if( rowVar->infimum().toString().size() > basic_var_infimum_width )
                        basic_var_infimum_width = rowVar->infimum().toString().size();
                    if( rowVar->supremum().toString().size() > basic_var_supremum_width )
                        basic_var_supremum_width = rowVar->supremum().toString().size();
                }
            }
            size_t table_width = basic_var_assign_width + basic_var_infimum_width + basic_var_supremum_width + basic_var_name_width + 8;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0  )
                {
                    columnWidths.push_back( 0 );
                    continue;
                }
                size_t column_width = columnVar->expression().toString( true, _friendlyNames ).size();
                if( columnVar->assignment().toString().size() > column_width )
                    column_width = columnVar->assignment().toString().size();
                if( columnVar->infimum().toString().size()+2 > column_width )
                    column_width = columnVar->infimum().toString().size()+2;
                if( columnVar->supremum().toString().size()+2 > column_width )
                    column_width = columnVar->supremum().toString().size()+2;
                Iterator columnIter = Iterator( columnVar->startEntry(), mpEntries );
                while( true )
                {
                    std::stringstream outA;
                    outA << (*columnIter).content();
                    if( outA.str().size() > column_width )
                        column_width = outA.str().size();
                    if( columnIter.vEnd( false ) )
                    {
                        break;
                    }
                    else
                    {
                        columnIter.vMove( false );
                    }
                }
                table_width += column_width + 3;
                columnWidths.push_back( column_width );
            }
            // Find the row and column number of the pivoting element.
            if( _pivotingElement != LAST_ENTRY_ID )
            {
                pivotingRow = (*mpEntries)[_pivotingElement].rowVar()->position();
                pivotingColumn = (*mpEntries)[_pivotingElement].columnVar()->position();
            }
            _out << _init << std::setw( (int) table_width ) << std::setfill( frameSign ) << "" << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream out;
                out << columnVar->expression().toString( true, _friendlyNames );
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << out.str();
                if(  _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) table_width ) << std::setfill( '-' ) << "" << std::endl;
            _out << std::setfill( ' ' );
            for( Variable<T1,T2>* rowVar : mRows )
            {
                size_t columnNumber = 0;
                _out << _init;
                if( rowVar != NULL )
                {
                    std::stringstream out;
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << "(" << rowVar->factor() << ")*(";
                    #endif
                    out << rowVar->expression().toString( true, _friendlyNames );
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << ")";
                    #endif
                    _out << std::setw( (int) basic_var_name_width ) << out.str();
                    if( _pivotingElement != LAST_ENTRY_ID && pivotingRow == rowVar->position() )
                        _out << " " << pivoting_separator;
                    else
                        _out << " " << separator;
                    Iterator rowIter = Iterator( rowVar->startEntry(), mpEntries );
                    size_t currentColumn = 0;
                    while( true )
                    {
                        for( size_t i = currentColumn; i < (*rowIter).columnVar()->position(); ++i )
                        {
                            if( mColumns[columnNumber]->size() != 0 )
                            {
                                _out << " ";
                                _out << std::setw( (int) columnWidths[columnNumber] ) << "0";
                                if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                                    _out << " " << pivoting_separator;
                                else
                                    _out << " " << separator;
                            }
                            ++columnNumber;
                        }
                        _out << " ";
                        std::stringstream out;
                        out << (*rowIter).content();
                        _out << std::setw( (int) columnWidths[columnNumber] ) << out.str();
                        if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                            _out << " " << pivoting_separator;
                        else
                            _out << " " << separator;
                        ++columnNumber;
                        currentColumn = (*rowIter).columnVar()->position()+1;
                        if( rowIter.hEnd( false ) )
                        {
                            for( size_t i = currentColumn; i < mWidth; ++i )
                            {
                                if( mColumns[columnNumber]->size() != 0 )
                                {
                                    _out << " ";
                                    _out << std::setw( (int) columnWidths[columnNumber] ) << "0";
                                    if( _pivotingElement != LAST_ENTRY_ID && (pivotingRow == rowVar->position() || pivotingColumn == columnNumber) )
                                        _out << " " << pivoting_separator;
                                    else
                                        _out << " " << separator;
                                }
                                ++columnNumber;
                            }
                            break;
                        }
                        rowIter.hMove( false );
                    }
                    _out << " ";
                    _out << std::setw( (int) basic_var_assign_width ) << rowVar->assignment().toString();
                    _out << " [";
                    _out << std::setw( (int) basic_var_infimum_width ) << rowVar->infimum().toString();
                    _out << ", ";
                    _out << std::setw( (int) basic_var_supremum_width ) << rowVar->supremum().toString();
                    _out << "]";
                    _out << std::endl;
                }
            }
            _out << _init << std::setw( (int) table_width ) << std::setfill( frameSign ) << "" << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << columnVar->assignment().toString();
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream outB;
                outB << "[" << columnVar->infimum().toString() << ",";
                _out << std::left << std::setw( (int) columnWidths[columnVar->position()] ) << outB.str();
                _out << std::right << "";
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << _init << std::setw( (int) basic_var_name_width ) << std::setfill( ' ' ) << "";
            _out << " " << separator;
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                if( columnVar->size() == 0 && !_withZeroColumns )
                    continue;
                _out << " ";
                std::stringstream outB;
                outB << " " << columnVar->supremum().toString() << "]";
                _out << std::setw( (int) columnWidths[columnVar->position()] ) << outB.str();
                if( _pivotingElement != LAST_ENTRY_ID && pivotingColumn == columnVar->position() )
                    _out << " " << pivoting_separator;
                else
                    _out << " " << separator;
            }
            _out << std::endl;
            _out << std::setfill( ' ' );
        }
    }    // end namspace lra
}    // end namspace smtrat

#endif   /* LRA_TABLEAU_H */
