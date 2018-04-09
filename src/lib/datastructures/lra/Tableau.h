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
#include <carl/util/IDPool.h>

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
                    Value<T1> newLimit;
                    ///
                    typename Bound<T1, T2>::BoundSet::const_iterator nextWeakerBound;
                    ///
                    std::vector< const Bound<T1, T2>*> premise;
                    
                    LearnedBound() = delete;
                    LearnedBound( const LearnedBound& ) = delete;
                    LearnedBound( LearnedBound&& _toMove ) :
                        newBound( _toMove.newBound ),
                        newLimit( std::move( _toMove.newLimit ) ),
                        nextWeakerBound( _toMove.nextWeakerBound ),
                        premise( std::move( _toMove.premise ) )
                    {}
                    LearnedBound( const Value<T1>& _limit, const Bound<T1, T2>* _newBound, typename Bound<T1, T2>::BoundSet::const_iterator _nextWeakerBound, std::vector< const Bound<T1, T2>*>&& _premise ):
                        newBound( _newBound ),
                        newLimit( _limit ),
                        nextWeakerBound( _nextWeakerBound ),
                        premise( std::move( _premise ) )
                    {}
                    
                    ~LearnedBound() {}
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
                size_t mVarIDCounter;
                ///
                ModuleInput::iterator mDefaultBoundPosition;
                ///
                std::stack<EntryID> mUnusedIDs;
                /// Id allocator for the variables.
                carl::IDPool mVariableIdAllocator;
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
                mutable T1 mCurDelta;
                ///
                carl::FastMap<carl::Variable, Variable<T1,T2>*> mOriginalVars;
                ///
                carl::FastPointerMap<typename Poly::PolyType, Variable<T1,T2>*> mSlackVars;
                ///
                carl::FastMap<FormulaT, std::vector<const Bound<T1, T2>*>*> mConstraintToBound;
                ///
                carl::FastPointerMap<Variable<T1,T2>, LearnedBound> mLearnedLowerBounds;
                ///
                carl::FastPointerMap<Variable<T1,T2>, LearnedBound> mLearnedUpperBounds;
                ///
                std::vector<typename carl::FastPointerMap<Variable<T1,T2>, LearnedBound>::iterator> mNewLearnedBounds;

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
                }
                
                /**
                 * @return 
                 */
                size_t size() const
                {
                    return mpEntries->size()-1;
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
                const carl::FastMap< carl::Variable, Variable<T1,T2>*>& originalVars() const
                {
                    return mOriginalVars;
                }
                
                /**
                 * @return 
                 */
                const carl::FastPointerMap<typename Poly::PolyType, Variable<T1,T2>*>& slackVars() const 
                {
                    return mSlackVars;
                }
                
                const T1& currentDelta() const
                {
                    return mCurDelta;
                }
                
                /**
                 * @return 
                 */
                const carl::FastMap<FormulaT, std::vector<const Bound<T1, T2>*>*>& constraintToBound() const
                {
                    return mConstraintToBound;
                }
                
                /**
                 * @return 
                 */
                carl::FastMap<FormulaT, std::vector<const Bound<T1, T2>*>*>& rConstraintToBound()
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
                carl::FastPointerMap<Variable<T1,T2>, LearnedBound>& rLearnedLowerBounds()
                {
                    return mLearnedLowerBounds;
                }

                /**
                 * @return 
                 */
                carl::FastPointerMap<Variable<T1,T2>, LearnedBound>& rLearnedUpperBounds()
                {
                    return mLearnedUpperBounds;
                }
                
                void resetTheta()
                {
                    *mpTheta = Value<T1>( T1( 0 ) );
                }
                
                /**
                 * @return 
                 */
                std::vector<typename carl::FastPointerMap<Variable<T1,T2>, LearnedBound>::iterator>& rNewLearnedBounds()
                {
                    return mNewLearnedBounds;
                }
                
                bool entryIsPositive( const TableauEntry<T1,T2>& _entry ) const
                {
                    if( Settings::omit_division )
                    {
                        const Variable<T1, T2>& basicVar = *_entry.rowVar();
                        return (_entry.content() > 0 && basicVar.factor() > 0) || (_entry.content() < 0 && basicVar.factor() < 0);
                    }
                    else
                        return _entry.content() > 0;
                }
                
                bool entryIsNegative( const TableauEntry<T1,T2>& _entry ) const
                {
                    if( Settings::omit_division )
                    {
                        const Variable<T1, T2>& basicVar = *_entry.rowVar();
                        return (_entry.content() < 0 && basicVar.factor() > 0) || (_entry.content() > 0 && basicVar.factor() < 0);
                    }
                    else
                        return _entry.content() < 0;
                }

                /**
                 * @return 
                 */
                FormulaT::const_iterator defaultBoundPosition() const
                {
                    return mDefaultBoundPosition;
                }
                
                bool isActive( const Variable<T1, T2>& _var ) const
                {
                    return _var.positionInNonActives() != mNonActiveBasics.end();
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
                
                Variable<T1,T2>* getVariable( const Poly& _lhs, T1& _factor, T1& _boundValue );
                
                Variable<T1,T2>* getObjectiveVariable( const Poly& _lhs );
                
                /**
                 * 
                 * @param _constraint
                 * @return 
                 */
                std::pair<const Bound<T1,T2>*, bool> newBound( const FormulaT& _constraint );
                void removeBound( const FormulaT& _constraint );
                
                /**
                 * 
                 * @param _bound
                 * @param _formula
                 */
                void activateBound( const Bound<T1,T2>* _bound, const FormulaT& _formula );
                
                /**
                 * 
                 * @param _variable
                 */
                void deleteVariable( Variable<T1, T2>* _variable, bool _optimizationVar = false );
                
                /**
                 * 
                 * @param _poly
                 * @param _isInteger
                 * @return 
                 */
                Variable<T1, T2>* newNonbasicVariable( const typename Poly::PolyType* _poly, bool _isInteger );
                
                /**
                 * 
                 * @param _poly
                 * @param _originalVars
                 * @param _isInteger
                 * @return 
                 */
                Variable<T1, T2>* newBasicVariable( const typename Poly::PolyType* _poly, bool _isInteger );
                
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
                EvalRationalMap getRationalAssignment() const;
                
                void adaptDelta( const Variable<T1,T2>& _variable, bool _upperBound, T1& _minDelta ) const;
                
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
                 * @param _objective
                 * @return 
                 */
                std::pair<EntryID,bool> optimizeIndependentNonbasics( const Variable<T1, T2>& _objective );
                
                /**
                 * 
                 * @return 
                 */
                std::pair<EntryID,bool> nextPivotingElementForOptimizing( const Variable<T1, T2>& _objective );
                std::pair<EntryID,bool> nextZeroPivotingElementForOptimizing( const Variable<T1, T2>& _objective ) const;
                
                /**
                 * 
                 * @param _basicVar
                 * @param _forIncreasingAssignment
                 * @return 
                 */
                EntryID isSuitable( const Variable<T1, T2>& _basicVar, bool _forIncreasingAssignment ) const;
                
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
                std::vector< std::vector< const Bound<T1, T2>* > > getConflictsFrom( EntryID _rowEntry ) const;
                
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
                Variable<T1, T2>* pivot( EntryID _pivotingElement, bool _optimizing = false );
                
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
                void update( bool _downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide, bool _optimizing = false );
                
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
                
                bool isConflicting() const;

                /**
                 * Creates a constraint referring to Gomory Cuts, if possible. 
                 * @param _ass
                 * @param _rowVar
                 * @return NULL,    if the cut can´t be constructed;
                 *         otherwise the valid constraint is returned.   
                 */
                const typename Poly::PolyType* gomoryCut( const T2& _ass, Variable<T1,T2>* _rowVar );
                
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
                void collect_premises( const Variable<T1,T2>* _rowVar, FormulasT& premises ) const;
                
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
