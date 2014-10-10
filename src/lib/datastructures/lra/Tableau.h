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
 * @file Tableau.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include <vector>
#include <stack>
#include <map>
#include <deque>
#include "Variable.h"

namespace smtrat
{
    namespace lra
    {
        /**
         * 
         */
        template<typename T1, typename T2>
        class TableauEntry
        {
            private:
                ///
                EntryID mUp;
                ///
                EntryID mDown;
                ///
                EntryID mLeft;
                ///
                EntryID mRight;
                ///
                Variable<T1, T2>* mRowVar;
                ///
                Variable<T1, T2>* mColumnVar;
                ///
                T2 mpContent;

            public:
                /**
                 * 
                 */
                TableauEntry():
                    mUp( LAST_ENTRY_ID ),
                    mDown( LAST_ENTRY_ID ),
                    mLeft( LAST_ENTRY_ID ),
                    mRight( LAST_ENTRY_ID ),
                    mRowVar( NULL ),
                    mColumnVar( NULL ),
                    mpContent()
                {}
                    
                /**
                 * 
                 * @param _up
                 * @param _down
                 * @param _left
                 * @param _right
                 * @param _rowVar
                 * @param _columnVar
                 * @param _content
                 */
                TableauEntry( EntryID _up, EntryID _down, EntryID _left, EntryID _right, Variable<T1, T2>* _rowVar, Variable<T1, T2>* _columnVar, const T2& _content ):
                    mUp( _up ),
                    mDown( _down ),
                    mLeft( _left ),
                    mRight( _right ),
                    mRowVar( _rowVar ),
                    mColumnVar( _columnVar ),
                    mpContent( _content )
                {}
                
                /**
                 * 
                 * @param _entry
                 */
                TableauEntry( const TableauEntry& _entry ):
                    mUp( _entry.mUp ),
                    mDown( _entry.mDown ),
                    mLeft( _entry.mLeft ),
                    mRight( _entry.mRight ),
                    mRowVar( _entry.mRowVar ),
                    mColumnVar( _entry.mColumnVar ),
                    mpContent( _entry.mpContent )
                {}
                
                /**
                 * 
                 */
                ~TableauEntry()
                {}
                
                /**
                 * 
                 * @param downwards
                 * @param _entryId
                 */
                void setVNext( bool downwards, const EntryID _entryId )
                {
                    if( downwards )
                        mDown = _entryId;
                    else
                        mUp = _entryId;
                }
                
                /**
                 * 
                 * @param leftwards
                 * @param _entryId
                 */
                void setHNext( bool leftwards, const EntryID _entryId )
                {
                    if( leftwards )
                        mLeft = _entryId;
                    else
                        mRight = _entryId;
                }
                
                /**
                 * 
                 * @param downwards
                 * @return 
                 */
                EntryID vNext( bool downwards )
                {
                    if( downwards )
                        return mDown;
                    else
                        return mUp;
                }
                
                /**
                 * 
                 * @param leftwards
                 * @return 
                 */
                EntryID hNext( bool leftwards )
                {
                    if( leftwards )
                        return mLeft;
                    else
                        return mRight;
                }

                /**
                 * @return 
                 */
                Variable<T1, T2>* rowVar() const
                {
                    return mRowVar;
                }

                /**
                 * 
                 * @param _rowVar
                 */
                void setRowVar( Variable<T1, T2>* _rowVar )
                {
                    mRowVar = _rowVar;
                }

                /**
                 * @return 
                 */
                Variable<T1, T2>* columnVar() const
                {
                    return mColumnVar;
                }

                /**
                 * 
                 * @param _columnVar
                 */
                void setColumnVar( Variable<T1, T2>* _columnVar )
                {
                    mColumnVar = _columnVar;
                }

                /**
                 * @return 
                 */
                const T2& content() const
                {
                    return mpContent;
                }

                /**
                 * @return 
                 */
                T2& rContent()
                {
                    return mpContent;
                }
        };

        /**
         * 
         */
        template<class Settings, typename T1, typename T2>
        class Tableau
        {
            public:
                /**
                 * 
                 */
                struct LearnedBound
                {
                    ///
                    const Bound<T1, T2>* newBound;
                    ///
                    const Bound<T1, T2>* nextWeakerBound;
                    ///
                    std::vector< const Bound<T1, T2>*> premise;
                };
            private:
                ///
                bool mRowsCompressed;
                ///
                size_t mWidth;
                ///
                size_t mPivotingSteps;
                ///
                size_t mMaxPivotsWithoutBlandsRule;
                ///
                ModuleInput::iterator mDefaultBoundPosition;
                ///
                std::stack<EntryID> mUnusedIDs;
                ///
                std::vector<Variable<T1,T2>*> mRows;       // First element is the head of the row and the second the length of the row.
                ///
                std::vector<Variable<T1,T2>*> mColumns;    // First element is the end of the column and the second the length of the column.
                ///
                std::list<std::list<std::pair<Variable<T1,T2>*,T2>>> mNonActiveBasics;
                ///
                std::vector<TableauEntry<T1,T2> >* mpEntries;
                ///
                std::vector<Variable<T1,T2>*> mConflictingRows;
                ///
                Value<T1>* mpTheta;
                ///
                std::map<carl::Variable, Variable<T1,T2>*> mOriginalVars;
                ///
                FastPointerMap<Polynomial, Variable<T1,T2>*> mSlackVars;
                ///
                FastPointerMap<Formula, std::vector<const Bound<T1, T2>*>*> mConstraintToBound;
                ///
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedLowerBounds;
                ///
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedUpperBounds;
                ///
                std::vector<typename std::map<Variable<T1,T2>*, LearnedBound>::iterator> mNewLearnedBounds;

                /**
                 *
                 */
                class Iterator
                {
                    private:
                        ///
                        EntryID mEntryID;
                        ///
                        std::vector<TableauEntry<T1,T2> >* mpEntries;

                    public:
                        /**
                         * 
                         * @param _start
                         * @param _entries
                         */
                        Iterator( EntryID _start, std::vector<TableauEntry<T1,T2> >* const _entries ):
                            mEntryID( _start ),
                            mpEntries( _entries )
                        {}
                        
                        /**
                         * 
                         * @param _iter
                         */
                        Iterator( const Iterator& _iter ):
                            mEntryID( _iter.entryID() ),
                            mpEntries( _iter.pEntries() )
                        {}

                        /**
                         * @return 
                         */
                        EntryID entryID() const
                        {
                            return mEntryID;
                        }

                        /**
                         * @return 
                         */
                        TableauEntry<T1,T2>& operator *()
                        {
                            return (*mpEntries)[mEntryID];
                        }
                        
                        /**
                         * @return 
                         */
                        bool vEnd( bool downwards ) const
                        {
                            return (*mpEntries)[mEntryID].vNext( downwards ) == LAST_ENTRY_ID;
                        }
                        
                        /**
                         * @return 
                         */
                        bool hEnd( bool leftwards ) const
                        {
                            return (*mpEntries)[mEntryID].hNext( leftwards ) == LAST_ENTRY_ID;
                        }

                        /**
                         * 
                         * @param downwards
                         */
                        void vMove( bool downwards )
                        {
                            assert( !vEnd( downwards ) );
                            mEntryID = (*mpEntries)[mEntryID].vNext( downwards );
                        }

                        /**
                         * 
                         * @param leftwards
                         */
                        void hMove( bool leftwards )
                        {
                            assert( !hEnd( leftwards ) );
                            mEntryID = (*mpEntries)[mEntryID].hNext( leftwards );
                        }

                        /**
                         * @return 
                         */
                        std::vector<TableauEntry<T1,T2> >* pEntries() const
                        {
                            return mpEntries;
                        }

                        /**
                         * @return 
                         */
                        bool operator ==( const Iterator& _iter ) const
                        {
                            return mEntryID == _iter.entryID();
                        }

                        /**
                         * @return 
                         */
                        bool operator !=( const Iterator& _iter ) const
                        {
                            return mEntryID != _iter.entryID();
                        }
                };    /* class Tableau<Settings,T1,T2>::Iterator */

            public:
                /**
                 * 
                 * @param _defaultBoundPosition
                 */
                Tableau( ModuleInput::iterator _defaultBoundPosition );
                
                /**
                 * 
                 */
                ~Tableau();

                /**
                 * 
                 * @param _expectedHeight
                 * @param _expectedWidth
                 * @param _expectedNumberOfBounds
                 */
                void setSize( size_t _expectedHeight, size_t _expectedWidth, size_t _expectedNumberOfBounds )
                {
                    mRows.reserve( _expectedHeight );
                    mColumns.reserve( _expectedWidth );
                    mpEntries->reserve( _expectedHeight*_expectedWidth+1 );
                    carl::reserve<T1>( 2*(_expectedNumberOfBounds+1) );
                    carl::reserve<T2>( _expectedHeight*_expectedWidth+1 );
                }
                
                /**
                 * @return 
                 */
                size_t size() const
                {
                    return mpEntries->size();
                }

                /**
                 * 
                 */
                void setBlandsRuleStart( size_t _start )
                {
                    mMaxPivotsWithoutBlandsRule = _start;
                }

                /**
                 * @return 
                 */
                const std::vector<Variable<T1, T2>*>& rows() const
                {
                    return mRows;
                }

                /**
                 * @return 
                 */
                const std::vector<Variable<T1, T2>*>& columns() const
                {
                    return mColumns;
                }
                
                /**
                 * @return 
                 */
                const std::map< carl::Variable, Variable<T1,T2>*>& originalVars() const
                {
                    return mOriginalVars;
                }
                
                /**
                 * @return 
                 */
                const FastPointerMap<Polynomial, Variable<T1,T2>*>& slackVars() const 
                {
                    return mSlackVars;
                }
                
                /**
                 * @return 
                 */
                const FastPointerMap<Formula, std::vector<const Bound<T1, T2>*>*>& constraintToBound() const
                {
                    return mConstraintToBound;
                }
                
                /**
                 * @return 
                 */
                FastPointerMap<Formula, std::vector<const Bound<T1, T2>*>*>& rConstraintToBound()
                {
                    return mConstraintToBound;
                }

                /**
                 * @return 
                 */
                size_t numberOfPivotingSteps() const
                {
                    return mPivotingSteps;
                }
                
                /**
                 * 
                 */
                void resetNumberOfPivotingSteps() 
                {
                    mPivotingSteps = 0;
                }

                /**
                 * @return 
                 */
                std::map<Variable<T1, T2>*, LearnedBound>& rLearnedLowerBounds()
                {
                    return mLearnedLowerBounds;
                }

                /**
                 * @return 
                 */
                std::map<Variable<T1, T2>*, LearnedBound>& rLearnedUpperBounds()
                {
                    return mLearnedUpperBounds;
                }
                
                /**
                 * @return 
                 */
                std::vector<typename std::map<Variable<T1, T2>*, LearnedBound>::iterator>& rNewLearnedBounds()
                {
                    return mNewLearnedBounds;
                }

                /**
                 * @return 
                 */
                smtrat::Formula::const_iterator defaultBoundPosition() const
                {
                    return mDefaultBoundPosition;
                }

                /**
                 * 
                 * @param _content
                 * @return 
                 */
                EntryID newTableauEntry( const T2& _content );
                
                /**
                 * 
                 * @param _entryID
                 */
                void removeEntry( EntryID _entryID );
                
                /**
                 * 
                 * @param _constraint
                 * @return 
                 */
                std::pair<const Bound<T1,T2>*, bool> newBound( const smtrat::Formula* _constraint );
                
                /**
                 * 
                 * @param _bound
                 * @param _formulas
                 */
                void activateBound( const Bound<T1,T2>* _bound, const PointerSet<Formula>& _formulas );
                
                /**
                 * 
                 * @param _poly
                 * @param _isInteger
                 * @return 
                 */
                Variable<T1, T2>* newNonbasicVariable( const smtrat::Polynomial* _poly, bool _isInteger );
                
                /**
                 * 
                 * @param _poly
                 * @param _originalVars
                 * @param _isInteger
                 * @return 
                 */
                Variable<T1, T2>* newBasicVariable( const smtrat::Polynomial* _poly, std::map<carl::Variable, Variable<T1, T2>*>& _originalVars, bool _isInteger );
                
                /**
                 * 
                 * @param nonbasic_coefficient_list
                 * @return 
                 */
                Variable<T1, T2>* newBasicVariable( std::vector<std::pair<size_t,T2>>& nonbasicindex_coefficient, const smtrat::Polynomial& poly, T2 leading_coeff, bool isInteger );
                
                /**
                 * g
                 * @param _var
                 */
                void activateBasicVar( Variable<T1, T2>* _var );
                
                /**
                 * 
                 * @param _var
                 */
                void deactivateBasicVar( Variable<T1, T2>* _var );
                
                /**
                 * 
                 */
                void storeAssignment();
                
                /**
                 * 
                 */
                void resetAssignment();
                
                /**
                 * 
                 * @return 
                 */
                smtrat::EvalRationalMap getRationalAssignment() const;
                
                /**
                 * 
                 */
                void compressRows();
                
                /**
                 * 
                 * @return 
                 */
                std::pair<EntryID, bool> nextPivotingElement();
                
                /**
                 * 
                 * @param _basicVar
                 * @param supremumViolated
                 * @return 
                 */
                std::pair<EntryID, bool> isSuitable( const Variable<T1, T2>& _basicVar, bool supremumViolated ) const;
                
                /**
                 * 
                 * @param _isBetter
                 * @param _than
                 * @return 
                 */
                bool betterEntry( EntryID _isBetter, EntryID _than ) const;
                
                /**
                 * 
                 * @param _rowEntry
                 * @return 
                 */
                std::vector< const Bound<T1, T2>* > getConflict( EntryID _rowEntry ) const;
                
                /**
                 * 
                 * @param _rowEntry
                 * @return 
                 */
                std::vector< std::set< const Bound<T1, T2>* > > getConflictsFrom( EntryID _rowEntry ) const;
                
                /**
                 * 
                 * @param _column
                 * @param _change
                 */
                void updateBasicAssignments( size_t _column, const Value<T1>& _change );
                
                /**
                 * 
                 * @param _pivotingElement
                 * @param updateAssignments
                 * @return 
                 */
                Variable<T1, T2>* pivot( EntryID _pivotingElement, bool updateAssignments = true );
                
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
                 * @param _updateAssignments If true, the assignments of all variables will be updated after pivoting.
                 */
                void update( bool _downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide, bool = true );
                
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
                void addToEntry( const T2& _toAdd, Iterator& _horiIter, bool _horiIterLeftFromVertIter, Iterator& _vertIter, bool _vertIterBelowHoriIter );
                
                /**
                 * Tries to refine the supremum and infimum of the given basic variable. 
                 * @param _basicVar The basic variable for which to refine the supremum and infimum.
                 */
                void rowRefinement( Variable<T1, T2>* _basicVar );

                /**
                 * 
                 * @param _var
                 * @param _term
                 * @return 
                 */
                typename std::map<carl::Variable, Variable<T1, T2>*>::iterator substitute( carl::Variable::Arg _var, const smtrat::Polynomial& _term );
                
                /**
                 * 
                 * @param _var
                 * @param _stopCriterium
                 * @return 
                 */
                size_t boundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium = 0 ) const;
                
                /**
                 * 
                 * @param _var
                 * @param _stopCriterium
                 * @return 
                 */
                size_t unboundedVariables( const Variable<T1,T2>& _var, size_t _stopCriterium = 0 ) const;
                
                /**
                 * 
                 * @return 
                 */
                size_t checkCorrectness() const;
                
                /**
                 * 
                 * @param _rowNumber
                 * @return 
                 */
                bool rowCorrect( size_t _rowNumber ) const;
                
                /**
                 * Checks whether a constraint is a defining constraint. 
                 * @param row_index
                 * @param max_value
                 * @return true, if the constraint is a defining constraint
                 *         false, otherwise   
                 */
                const smtrat::Constraint* isDefining( size_t row_index, std::vector<std::pair<size_t,T2>>& nonbasicindex_coefficient_list, T2 lcm, T2& max_value ) const;
                
                /**
                 * Checks whether the row with index row_index is defining. 
                 * @param dc_positions
                 * @param row_index
                 * @return true, if so
                 *         false, otherwise   
                 */ 
                bool isDefining_Easy( std::vector<size_t>& dc_positions, size_t row_index );
                
                /**
                 * Checks whether the column with index column_index is a diagonal column.
                 * @param column_index
                 * @param diagonals
                 * @return true, if the column with index column_index is a diagonal column
                 *         false, otherwise   
                 */        
                bool isDiagonal( size_t column_index, std::vector<size_t>& diagonals );
                
                /**
                 * @param row_index
                 * @param dc_positions
                 * @return The row of the defining constraint with index row_index in the Tableau containing this DC.
                 */ 
                size_t position_DC( size_t row_index, std::vector<size_t>& dc_positions );
                
                /**
                 * @param column_index
                 * @param diagonals
                 * @return The the actual index of the column with index column_index in the permutated tableau.   
                 */   
                size_t revert_diagonals( size_t column_index, std::vector<size_t>& diagonals );
                
                /**
                 * Multiplies all entries in the column with the index column_index by (-1).
                 * @param column_index
                 */     
                void invertColumn( size_t column_index );
                
                /**
                 * Adds the column with index columnB_index multiplied by multiple to the column with index columnA_index.
                 * @param columnA_index
                 * @param columnB_index
                 * @param multiple
                 */
                void addColumns( size_t columnA_index, size_t columnB_index, T2 multiple );
                
                /**
                 * Multiplies the row with index row_index by multiple.
                 * @param row_index
                 * @param multiple
                 */        
                void multiplyRow( size_t row_index, T2 multiple );
                
                /**
                 * Calculates the scalar product of the row with index rowA from Tableau A with the column
                 * with index columnB from Tableau B considering that the columns in B are permutated.
                 * @param A
                 * @param B
                 * @param rowA
                 * @param columnB
                 * @param diagonals
                 * @param dc_positions 
                 * @return the value (T) of the scalar product.
                 */        
                std::pair< const Variable<T1,T2>*, T2 > Scalar_Product( Tableau<Settings,T1,T2>& A, Tableau<Settings,T1,T2>& B, size_t rowA, size_t columnB, std::vector<size_t>& diagonals, std::vector<size_t>& dc_positions );
                
                /**
                 * Calculate the Hermite normal form of the calling Tableau. 
                 * @param diagonals
                 * @param full_rank
                 * @return The vector containing the indices of the diagonal elements.
                 */
                void calculate_hermite_normalform( std::vector<size_t>& diagonals, bool& full_rank );
                
                /**
                 * Inverts the HNF matrix.
                 * @param diagonals
                 */
                void invert_HNF_Matrix( std::vector<size_t>& diagonals );
                
                /**
                 * Checks whether a cut from proof can be constructed with the row with index row_index in the DC_Tableau. 
                 * @param Inverted_Tableau
                 * @param DC_Tableau
                 * @param row_index
                 * @param diagonals
                 * @param dc_positions
                 * @param lower
                 * @param max_value
                 * @return the valid proof,    if the proof can be constructed.
                 *         NULL,               otherwise.   
                 */
                smtrat::Polynomial* create_cut_from_proof( Tableau<Settings,T1,T2>& Inverted_Tableau, Tableau<Settings,T1,T2>& DC_Tableau, size_t row_index, std::vector<size_t>& diagonals, std::vector<size_t>& dc_positions, T2& lower, T2& max_value );

                /**
                 * Creates a constraint referring to Gomory Cuts, if possible. 
                 * @param _ass
                 * @param _rowVar
                 * @return NULL,    if the cut can´t be constructed;
                 *         otherwise the valid constraint is returned.   
                 */
                const smtrat::Polynomial* gomoryCut( const T2& _ass, Variable<T1,T2>* _rowVar );
                
                /**
                 * @param _rowVar
                 * @return number of entries in the row belonging to _rowVar
                 */
                size_t getNumberOfEntries( Variable<T1,T2>* _rowVar );
                
                /**
                 * Collects the premises for branch and bound and stores them in premises.  
                 * @param _rowVar
                 * @param premises
                 */
                void collect_premises( const Variable<T1,T2>* _rowVar, PointerSet<Formula>& premises );
                
                /**
                 * 
                 * @param _out
                 * @param _maxEntryLength
                 * @param _init
                 */
                void printHeap( std::ostream& _out = std::cout, int _maxEntryLength = 30, const std::string  _init = "" ) const;

                /**
                 * 
                 * @param _entry
                 * @param _out
                 * @param _maxEntryLength
                 */
                void printEntry( EntryID _entry, std::ostream& _out = std::cout, int _maxEntryLength = 20 ) const;

                /**
                 * 
                 * @param _allBounds
                 * @param _out
                 * @param _init
                 */
                void printVariables( bool _allBounds = true, std::ostream& _out = std::cout, const std::string _init = "" ) const;
                
                /**
                 * 
                 * @param _init
                 * @param _out
                 */
                void printLearnedBounds( const std::string _init = "", std::ostream& _out = std::cout ) const;
 
                /**
                 * 
                 * @param _var
                 * @param _learnedBound
                 * @param _init
                 * @param _out
                 */
                void printLearnedBound( const Variable<T1,T2>& _var, const LearnedBound& _learnedBound, const std::string _init = "", std::ostream& _out = std::cout ) const;
                 
                /**
                 * 
                 * @param _pivotingElement
                 * @param _out
                 * @param _init
                 * @param _friendlyNames
                 * @param _withZeroColumns
                 */
                void print( EntryID _pivotingElement = LAST_ENTRY_ID, std::ostream& _out = std::cout, const std::string _init = "", bool _friendlyNames = true, bool _withZeroColumns = false ) const;

        };
    }    // end namspace lra
}    // end namspace smtrat

#include "Tableau.tpp"

