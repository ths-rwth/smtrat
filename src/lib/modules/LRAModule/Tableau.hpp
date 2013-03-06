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
 *
 * @version 2012-04-05
 * Created on November 14th, 2012
 */

#ifndef TLRA_TABLEAU_H
#define TLRA_TABLEAU_H

#include <vector>
#include <stack>
#include <map>
#include "Variable.h"

#define TLRA_USE_PIVOTING_STRATEGY
#define TLRA_REFINEMENT
//#define TLRA_PRINT_STATS
//#define TLRA_USE_OCCURENCE_STRATEGY
#ifndef TLRA_USE_OCCURENCE_STRATEGY
#define TLRA_USE_THETA_STRATEGY
#endif
#define TLRA_INTRODUCE_NEW_CONSTRAINTS

// TODO: Make it templated, such that the coefficients, bounds and assignments can be any kind of arithmetic data type.
//       You could also use double, once assuring they under approximate and a satisfiable result is indeed satisfiable,
//       and once assuring they over approximate and a unsatisfiable result is indeed unsatisfiable.

namespace tlra
{
    typedef unsigned EntryID;

    template<class T>
    class TableauEntry
    {
        private:
            EntryID  mUp;
            EntryID  mDown;
            EntryID  mLeft;
            EntryID  mRight;
            unsigned mRowNumber;
            unsigned mColumnNumber;
            T        mpContent;

        public:
            TableauEntry():
                mUp( 0 ),
                mDown( 0 ),
                mLeft( 0 ),
                mRight( 0 ),
                mRowNumber( 0 ),
                mColumnNumber( 0 ),
                mpContent( 0 )
            {}
            ;
            TableauEntry( EntryID _up,
                          EntryID _down,
                          EntryID _left,
                          EntryID _right,
                          unsigned _rowNumber,
                          unsigned _columnNumber,
                          T _content ):
                mUp( _up ),
                mDown( _down ),
                mLeft( _left ),
                mRight( _right ),
                mRowNumber( _rowNumber ),
                mColumnNumber( _columnNumber ),
                mpContent( _content )
            {}
            ;
            ~TableauEntry()
            {}
            ;

            EntryID up() const
            {
                return mUp;
            }

            void setUp( const EntryID _up )
            {
                mUp = _up;
            }

            EntryID down() const
            {
                return mDown;
            }

            void setDown( const EntryID _down )
            {
                mDown = _down;
            }

            EntryID left() const
            {
                return mLeft;
            }

            void setLeft( const EntryID _left )
            {
                mLeft = _left;
            }

            EntryID right() const
            {
                return mRight;
            }

            void setRight( const EntryID _right )
            {
                mRight = _right;
            }

            unsigned rowNumber() const
            {
                return mRowNumber;
            }

            void setRowNumber( unsigned _rowNumber )
            {
                mRowNumber = _rowNumber;
            }

            unsigned columnNumber() const
            {
                return mColumnNumber;
            }

            void setColumnNumber( unsigned _columnNumber )
            {
                mColumnNumber = _columnNumber;
            }

            const T& content() const
            {
                return mpContent;
            }

            T& rContent()
            {
                return mpContent;
            }
    };

    template <class T> class Tableau
    {
        public:
            struct LearnedBound
            {
                const Bound<T>* newBound;
                const Bound<T>* nextWeakerBound;
                std::vector< const Bound<T>*>* premise;
            };
        private:
            struct TableauHead
            {
                EntryID   mStartEntry;
                unsigned  mSize;
                Variable<T>* mName;
                unsigned  mActivity;
            };
            unsigned                   mHeight;
            unsigned                   mWidth;
            unsigned                   mPivotingSteps;
            #ifdef TLRA_USE_PIVOTING_STRATEGY
            unsigned                   mRestarts;
            unsigned                   mNextRestartBegin;
            unsigned                   mNextRestartEnd;
            #endif
            smtrat::Formula::iterator  mDefaultBoundPosition;
            std::stack<EntryID>        mUnusedIDs;
            std::vector<TableauHead>   mRows;       // First element is the head of the row and the second the length of the row.
            std::vector<TableauHead>   mColumns;    // First element is the end of the column and the second the length of the column.
            std::set< unsigned >       mActiveRows;
            std::vector<TableauEntry<T> >* mpEntries;
            Value<T>*                     mpTheta;
            #ifdef TLRA_REFINEMENT
            std::vector<LearnedBound>  mLearnedBounds;
            #endif

            class Iterator
            {
                private:
                    unsigned                   mEntryID;
                    std::vector<TableauEntry<T> >* mpEntries;

                public:
                    Iterator( EntryID _start, std::vector<TableauEntry<T> >* const _entries ):
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

                    TableauEntry<T>& operator *()
                    {
                        return (*mpEntries)[mEntryID];
                    }

                    bool rowBegin() const
                    {
                        return (*mpEntries)[mEntryID].left() == 0;
                    }

                    bool rowEnd() const
                    {
                        return (*mpEntries)[mEntryID].right() == 0;
                    }

                    bool columnBegin() const
                    {
                        return (*mpEntries)[mEntryID].up() == 0;
                    }

                    bool columnEnd() const
                    {
                        return (*mpEntries)[mEntryID].down() == 0;
                    }

                    void up()
                    {
                        assert( !columnBegin() );
                        mEntryID = (*mpEntries)[mEntryID].up();
                    }

                    void down()
                    {
                        assert( !columnEnd() );
                        mEntryID = (*mpEntries)[mEntryID].down();
                    }

                    void left()
                    {
                        assert( !rowBegin() );
                        mEntryID = (*mpEntries)[mEntryID].left();
                    }

                    void right()
                    {
                        assert( !rowEnd() );
                        mEntryID = (*mpEntries)[mEntryID].right();
                    }

                    std::vector<TableauEntry<T> >* const pEntries() const
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
            };    /* class Tableau<T>::Iterator */

        public:
            Tableau( smtrat::Formula::iterator );
            ~Tableau();

            void setSize( unsigned _expectedHeight, unsigned _expectedWidth )
            {
                mRows.reserve( _expectedHeight );
                mColumns.reserve( _expectedWidth );
                mpEntries->reserve( _expectedHeight*_expectedWidth+1 );
            }

            #ifdef TLRA_USE_PIVOTING_STRATEGY
            void setBlandsRuleStart( unsigned _start )
            {
                mNextRestartEnd = _start;
            }
            #endif

            const std::vector<TableauHead>& rows() const
            {
                return mRows;
            }

            const std::vector<TableauHead>& columns() const
            {
                return mColumns;
            }

            void incrementBasicActivity( const Variable<T>& _var )
            {
                if( mRows[_var.position()].mActivity++ == 0 )
                {
                    mActiveRows.insert( _var.position() );
                }
            }

            void incrementNonbasicActivity( const Variable<T>& _var )
            {
                ++mColumns[_var.position()].mActivity;
            }

            void decrementBasicActivity( const Variable<T>& _var )
            {
                assert( mRows[_var.position()].mActivity != 0 );
                if( --mRows[_var.position()].mActivity == 0 )
                {
                    mActiveRows.erase( _var.position() );
                }
            }

            void decrementNonbasicActivity( const Variable<T>& _var )
            {
                assert( mColumns[_var.position()].mActivity != 0 );
                --mColumns[_var.position()].mActivity;
            }

            unsigned numberOfPivotingSteps() const
            {
                return mPivotingSteps;
            }

            #ifdef TLRA_REFINEMENT
            std::vector<LearnedBound>& rLearnedBounds()
            {
                return mLearnedBounds;
            }
            #endif

            smtrat::Formula::const_iterator defaultBoundPosition() const
            {
                return mDefaultBoundPosition;
            }

            EntryID newTableauEntry();
            void removeEntry( EntryID );
            Variable<T>* newNonbasicVariable( const GiNaC::ex* );
            Variable<T>* newBasicVariable( const GiNaC::ex*, const std::vector<Variable<T>*>&, std::vector<T>& );
            std::pair<EntryID, bool> nextPivotingElement();
            std::pair<EntryID, bool> isSuitable( EntryID, Value<T>& ) const;
            bool betterEntry( EntryID, EntryID ) const;
            std::vector< const Bound<T>* > getConflict( EntryID ) const;
            std::vector< std::set< const Bound<T>* > > getConflictsFrom( EntryID ) const;
            void updateBasicAssignments( unsigned, const Value<T>& );
            void pivot( EntryID );
            void updateDownwards( EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
            void updateUpwards( EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
            #ifdef TLRA_REFINEMENT
            void rowRefinement( const TableauHead& );
            void columnRefinement( const TableauHead& );
            void exhaustiveRefinement();
            #endif
            unsigned checkCorrectness() const;
            bool rowCorrect( unsigned _rowNumber ) const;
            void printHeap( std::ostream& = std::cout, unsigned = 30, const std::string = "" ) const;
            void printEntry( std::ostream& = std::cout, EntryID = 0, unsigned = 20 ) const;
            void printVariables( std::ostream& = std::cout, const std::string = "" ) const;
            void printLearnedBounds( const std::string = "", std::ostream& = std::cout ) const;
            void print( std::ostream& = std::cout, unsigned = 28, const std::string = "" ) const;

    };

    template<class T>
    Tableau<T>::Tableau( smtrat::Formula::iterator _defaultBoundPosition ):
        mHeight( 0 ),
        mWidth( 0 ),
        mPivotingSteps( 0 ),
        #ifdef TLRA_USE_PIVOTING_STRATEGY
        mRestarts( 0 ),
        mNextRestartBegin( 0 ),
        mNextRestartEnd( 0 ),
        #endif
        mDefaultBoundPosition( _defaultBoundPosition ),
        mUnusedIDs(),
        mRows(),
        mColumns(),
        mActiveRows()
        #ifdef TLRA_REFINEMENT
        ,
        mLearnedBounds()
        #endif
    {
        mpEntries = new std::vector< TableauEntry<T> >();
        mpEntries->push_back( TableauEntry<T>() );
        mpTheta = new Value<T>();
    };

    template<class T>
    Tableau<T>::~Tableau()
    {
        #ifdef TLRA_PRINT_STATS
        std::cout << "#Pivoting steps:  " << mPivotingSteps << std::endl;
        std::cout << "#Tableus entries: " << mpEntries->size()-1 << std::endl;
        std::cout << "Tableau coverage: " << (double)(mpEntries->size()-1)/(double)(mRows.size()*mColumns.size())*100 << "%" << std::endl;
        #endif
        while( !mRows.empty() )
        {
            Variable<T>* varToDel = mRows.back().mName;
            mRows.pop_back();
            delete varToDel;
        }
        while( !mColumns.empty() )
        {
            Variable<T>* varToDel = mColumns.back().mName;
            mColumns.pop_back();
            delete varToDel;
        }
        while( !mUnusedIDs.empty() )
        {
            mUnusedIDs.pop();
        }
        delete mpEntries;
        delete mpTheta;
    };

    /**
     *
     * @return
     */
    template<class T>
    EntryID Tableau<T>::newTableauEntry()
    {
        if( mUnusedIDs.empty() )
        {
            mpEntries->push_back( TableauEntry<T>( 0, 0, 0, 0, 0, 0, T( 0 ) ) );
            return (mpEntries->size() - 1);
        }
        else
        {
            EntryID id = mUnusedIDs.top();
            mUnusedIDs.pop();
            return id;
        }
    }

    /**
     *
     * @param _entryID
     */
    template<class T>
    void Tableau<T>::removeEntry( EntryID _entryID )
    {
        TableauEntry<T>& entry = (*mpEntries)[_entryID];
        TableauHead& rowHead = mRows[entry.rowNumber()];
        TableauHead& columnHead = mColumns[entry.columnNumber()];
        const EntryID& up = entry.up();
        const EntryID& down = entry.down();
        if( up != 0 )
        {
            (*mpEntries)[up].setDown( down );
        }
        if( down != 0 )
        {
            (*mpEntries)[down].setUp( up );
        }
        else
        {
            columnHead.mStartEntry = up;
        }
        const EntryID& left = entry.left();
        const EntryID& right = entry.right();
        if( left != 0 )
        {
            (*mpEntries)[left].setRight( right );
        }
        else
        {
            rowHead.mStartEntry = right;
        }
        if( right != 0 )
        {
            (*mpEntries)[right].setLeft( left );
        }
        --rowHead.mSize;
        --columnHead.mSize;
        mUnusedIDs.push( _entryID );
    }

    /**
     *
     * @param _ex
     * @return
     */
    template<class T>
    Variable<T>* Tableau<T>::newNonbasicVariable( const GiNaC::ex* _ex )
    {
        Variable<T>* var = new Variable<T>( mWidth++, false, _ex, mDefaultBoundPosition );
        mColumns.push_back( TableauHead() );
        mColumns[mWidth-1].mStartEntry = 0;
        mColumns[mWidth-1].mSize = 0;
        mColumns[mWidth-1].mName = var;
        return var;
    }

    /**
     *
     * @param _ex
     * @param _nonbasicVariables
     * @param _coefficients
     * @return
     */
    template<class T>
    Variable<T>* Tableau<T>::newBasicVariable( const GiNaC::ex* _ex, const std::vector< Variable<T>* >& _nonbasicVariables, std::vector< T >& _coefficients )
    {
        assert( _coefficients.size() == _coefficients.size() );
        Variable<T>* var = new Variable<T>( mHeight++, true, _ex, mDefaultBoundPosition );
        mRows.push_back( TableauHead() );
        EntryID currentStartEntryOfRow = 0;
        class std::vector< Variable<T>* >::const_iterator basicVar = _nonbasicVariables.begin();
        class std::vector< T >::iterator coeff = _coefficients.begin();
        while( basicVar != _nonbasicVariables.end() )
        {
            EntryID entryID = newTableauEntry();
            TableauEntry<T>& entry = (*mpEntries)[entryID];
            // Fix the position.
            entry.setColumnNumber( (*basicVar)->position() );
            entry.setRowNumber( mHeight-1 );
            // Set the content.
            entry.rContent() = *coeff;
            TableauHead& columnHead = mColumns[entry.columnNumber()];
            EntryID& columnStart = columnHead.mStartEntry;
            // Set it as column end.
            if( columnStart != 0 )
            {
                (*mpEntries)[columnStart].setDown( entryID );
            }
            entry.setUp( columnStart );
            columnStart = entryID;
            ++columnHead.mSize;
            entry.setDown( 0 );
            // Put it in the row.
            if( currentStartEntryOfRow == 0 )
            {
                currentStartEntryOfRow = entryID;
            }
            else
            {
                Iterator rowIter = Iterator( currentStartEntryOfRow, mpEntries );
                while( !rowIter.rowEnd() && (*rowIter).columnNumber() < entry.columnNumber() )
                {
                    rowIter.right();
                }
                assert( (*rowIter).columnNumber() !=  entry.columnNumber() );
                if( (*rowIter).columnNumber() > entry.columnNumber() )
                {
                    // Entry horizontally between two entries.
                    EntryID leftEntryID = (*rowIter).left();
                    if( leftEntryID != 0 )
                    {
                        (*mpEntries)[leftEntryID].setRight( entryID );
                    }
                    (*rowIter).setLeft( entryID );
                    entry.setLeft( leftEntryID );
                    entry.setRight( rowIter.entryID() );
                    if( leftEntryID == 0 )
                    {
                        currentStartEntryOfRow = entryID;
                    }
                }
                else
                {
                    // Entry will be the rightmost in this row.
                    (*rowIter).setRight( entryID );
                    entry.setLeft( rowIter.entryID() );
                    entry.setRight( 0 );
                }
            }
            ++basicVar;
            ++coeff;
        }
        TableauHead& rowHead = mRows[mHeight-1];
        rowHead.mStartEntry = currentStartEntryOfRow;
        rowHead.mSize = _nonbasicVariables.size();
        rowHead.mName = var;
        return var;
    }

    #ifdef TLRA_USE_PIVOTING_STRATEGY
//    /**
//     *
//     * @param y
//     * @param x
//     * @return
//     */
//    template<class T>
//    static unsigned luby( unsigned _numberOfRestarts )
//    {
//        // Find the finite subsequence that contains index 'x', and the
//        // size of that subsequence:
//        std::cout << "_numberOfRestarts = " << _numberOfRestarts;
//        unsigned size, seq;
//        for( size = 1, seq = 0; size < _numberOfRestarts + 1; seq++, size = 2 * size + 1 );
//
//        while( size - 1 != _numberOfRestarts )
//        {
//            size = (size - 1) >> 1;
//            seq--;
//            _numberOfRestarts = _numberOfRestarts % size;
//        }
//        std::cout << " results in seq = " << seq << std::endl;
//        if( seq >= 64 ) return 0;
//        std::cout << " results in seq = " << seq << std::endl;
//        unsigned result = 1;
//        result = result << seq;
//        std::cout << "result = " << result << std::endl;
//        return result;
//    }
    #endif

    /**
     *
     * @return
     */
    template<class T>
    std::pair<EntryID,bool> Tableau<T>::nextPivotingElement()
    {
        #ifdef TLRA_USE_PIVOTING_STRATEGY
        //  Dynamic strategy for a fixed number of steps
//        if( mPivotingSteps >= mNextRestartBegin && mPivotingSteps < mNextRestartEnd )
        if( mPivotingSteps < mNextRestartEnd )
        {
            #ifdef TLRA_USE_OCCURENCE_STRATEGY
            unsigned smallestRowSize = mWidth;
            unsigned smallestColumnSize = mHeight;
            #endif
            EntryID beginOfBestRow = 0;
            EntryID beginOfFirstConflictRow = 0;
            *mpTheta = Value<T>( 0 );
            for( auto rowNumber = mActiveRows.begin(); rowNumber != mActiveRows.end(); ++rowNumber )
            {
                Value<T> theta = Value<T>();
                std::pair<EntryID,bool> result = isSuitable( *rowNumber, theta );
                if( !result.second )
                {
                    // Found a conflicting row.
                    if( beginOfFirstConflictRow == 0 || theta.mainPart() > mpTheta->mainPart() )
                    {
                        *mpTheta = theta;
                        beginOfFirstConflictRow = result.first;
                    }
                }
                else if( result.first != 0 )
                {
                    #ifdef TLRA_USE_THETA_STRATEGY
                    if( beginOfBestRow == 0 || abs( theta.mainPart().ginacNumeric() ) > abs( mpTheta->mainPart().ginacNumeric() ) )
                    {
                        beginOfBestRow = result.first;
                        *mpTheta = theta;
                    }
                    #endif
                    #ifdef TLRA_USE_OCCURENCE_STRATEGY
                    if( mRows[(*mpEntries)[result.first].rowNumber()].mSize < smallestRowSize )
                    {
                        // Found a better pivoting element.
                        smallestRowSize = mRows[(*mpEntries)[result.first].rowNumber()].mSize;
                        smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                        beginOfBestRow = result.first;
                        *mpTheta = theta;
                    }
                    else if( mRows[(*mpEntries)[result.first].rowNumber()].mSize == smallestRowSize
                             && mColumns[(*mpEntries)[result.first].columnNumber()].mSize < smallestColumnSize )
                    {
                        // Found a better pivoting element.
                        smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                        beginOfBestRow = result.first;
                        *mpTheta = theta;
                    }
                    #endif
                }
            }
            if( beginOfBestRow == 0 && beginOfFirstConflictRow != 0 )
            {
                // The best pivoting element found
                return std::pair<EntryID,bool>( beginOfFirstConflictRow, false );
            }
            else if( beginOfBestRow != 0 )
            {
                // The best pivoting element found
                return std::pair<EntryID,bool>( beginOfBestRow, true );
            }
            else
            {
                // Found no pivoting element, that is no variable violates its bounds.
                return std::pair<EntryID,bool>( 0, true );
            }
        }
        // Bland's rule
        else
        {
//            if( mPivotingSteps == mNextRestartEnd )
//            {
//                mNextRestartBegin = mNextRestartEnd + mWidth * luby( mRestarts++ );
//                mNextRestartEnd = mNextRestartBegin + mWidth;
//                std::cout << "Next restart range = [" << mNextRestartBegin << "," << mNextRestartEnd << "]" << std::endl;
//            }
        #endif
            for( auto rowNumber = mActiveRows.begin(); rowNumber != mActiveRows.end(); ++rowNumber )
            {
                std::pair<EntryID,bool> result = isSuitable( *rowNumber, *mpTheta );
                if( !result.second )
                {
                    // Found a conflicting row.
                    return std::pair<EntryID,bool>( result.first, false );
                }
                else if( result.first != 0 )
                {
                    // Found a pivoting element
                    return std::pair<EntryID,bool>( result.first, true );
                }
            }
            // Found no pivoting element, that is no variable violates its bounds.
            return std::pair<EntryID,bool>( 0, true );
        #ifdef TLRA_USE_PIVOTING_STRATEGY
        }
        #endif
    }

    /**
     *
     * @param _rowNumber
     * @return
     */
    template<class T>
    std::pair<EntryID,bool> Tableau<T>::isSuitable( unsigned _rowNumber, Value<T>& _theta ) const
    {
        EntryID bestEntry = 0;
        const TableauHead& _rowHead = mRows[_rowNumber];
        const Variable<T>& basicVar = *_rowHead.mName;
        const Bound<T>& basicVarSupremum = basicVar.supremum();
        const Value<T>& basicVarAssignment = basicVar.assignment();
        const Bound<T>& basicVarInfimum = basicVar.infimum();
        const EntryID& rowStartEntry = _rowHead.mStartEntry;
        // Upper bound is violated
        if( basicVarSupremum < basicVarAssignment )
        {
            // Check all entries in the row / nonbasic variables
            Iterator rowIter = Iterator( rowStartEntry, mpEntries );
            while( true )
            {
                const Variable<T>& nonBasicVar = *mColumns[(*rowIter).columnNumber()].mName;
                if( (*rowIter).content().isNegative())
                {
                    if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                    {
                        // Nonbasic variable suitable
                        assert( (*rowIter).content() != 0 );
                        if( betterEntry( rowIter.entryID(), bestEntry ) )
                        {
                            _theta = (basicVarSupremum.limit() - basicVarAssignment)/(*rowIter).content();
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
                            _theta = (basicVarSupremum.limit() - basicVarAssignment)/(*rowIter).content();
                            bestEntry = rowIter.entryID();
                        }
                    }
                }
                if( rowIter.rowEnd() )
                {
                    if( bestEntry == 0 )
                    {
                        _theta = basicVarAssignment - basicVarSupremum.limit();
                        return std::pair<EntryID,bool>( rowStartEntry, false );
                    }
                    break;
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        // Lower bound is violated
        else if( basicVarInfimum > basicVarAssignment )
        {
            // Check all entries in the row / nonbasic variables
            Iterator rowIter = Iterator( rowStartEntry, mpEntries );
            while( true )
            {
                const Variable<T>& nonBasicVar = *mColumns[(*rowIter).columnNumber()].mName;
                if( (*rowIter).content().isPositive())
                {
                    if( nonBasicVar.supremum() > nonBasicVar.assignment() )
                    {
                        // Nonbasic variable suitable
                        assert( (*rowIter).content() != 0 );
                        if( betterEntry( rowIter.entryID(), bestEntry ) )
                        {
                            _theta = (basicVarInfimum.limit() - basicVarAssignment)/(*rowIter).content();
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
                            _theta = (basicVarInfimum.limit() - basicVarAssignment)/(*rowIter).content();
                            bestEntry = rowIter.entryID();
                        }
                    }
                }
                if( rowIter.rowEnd() )
                {
                    if( bestEntry == 0 )
                    {
                        _theta = basicVarInfimum.limit() - basicVarAssignment;
                        return std::pair<EntryID,bool>( rowStartEntry, false );
                    }
                    break;
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        return std::pair<EntryID,bool>( bestEntry, true );
    }

    template<class T>
    bool Tableau<T>::betterEntry( EntryID _isBetter, EntryID _than ) const
    {
        assert( _isBetter != 0 );
        if( _than == 0 ) return true;
        const TableauHead& isBetterColumn = mColumns[(*mpEntries)[_isBetter].columnNumber()];
        const TableauHead& thanColumn = mColumns[(*mpEntries)[_than].columnNumber()];
        if( isBetterColumn.mActivity < thanColumn.mActivity ) return true;
        else if( isBetterColumn.mActivity == thanColumn.mActivity )
        {
            if( isBetterColumn.mSize < thanColumn.mSize ) return true;
        }
        return false;
    }

    /**
     *
     * @param _startRow
     * @return
     */
    template<class T>
    std::vector< const Bound<T>* > Tableau<T>::getConflict( EntryID _rowEntry ) const
    {
        assert( _rowEntry != 0 );
        const TableauHead& row = mRows[(*mpEntries)[_rowEntry].rowNumber()];
        // Upper bound is violated
        std::vector< const Bound<T>* > conflict = std::vector< const Bound<T>* >();
        if( row.mName->supremum() < row.mName->assignment() )
        {
            conflict.push_back( row.mName->pSupremum() );
            // Check all entries in the row / basic variables
            Iterator rowIter = Iterator( row.mStartEntry, mpEntries );
            while( true )
            {
                if( (*rowIter).content().isNegative() )
                {
                    assert( !(mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment()) );
                    conflict.push_back( mColumns[(*rowIter).columnNumber()].mName->pSupremum() );
                }
                else
                {
                    assert( !(mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment()) );
                    conflict.push_back( mColumns[(*rowIter).columnNumber()].mName->pInfimum() );
                }
                if( rowIter.rowEnd() )
                {
                    break;
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        // Lower bound is violated
        else
        {
            assert( row.mName->infimum() > row.mName->assignment() );
            conflict.push_back( row.mName->pInfimum() );
            // Check all entries in the row / basic variables
            Iterator rowIter = Iterator( row.mStartEntry, mpEntries );
            while( true )
            {
                if( (*rowIter).content().isPositive() )
                {
                    assert( !(mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment()) );
                    conflict.push_back( mColumns[(*rowIter).columnNumber()].mName->pSupremum() );
                }
                else
                {
                    assert( !(mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment()) );
                    conflict.push_back( mColumns[(*rowIter).columnNumber()].mName->pInfimum() );
                }
                if( rowIter.rowEnd() )
                {
                    break;
                }
                else
                {
                    rowIter.right();
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
    template<class T>
    std::vector< std::set< const Bound<T>* > > Tableau<T>::getConflictsFrom( EntryID _rowEntry ) const
    {
        std::vector< std::set< const Bound<T>* > > conflicts = std::vector< std::set< const Bound<T>* > >();
        for( unsigned rowNumber = (*mpEntries)[_rowEntry].rowNumber(); rowNumber < mRows.size(); ++rowNumber )
        {
            // Upper bound is violated
            if( mRows[rowNumber].mName->supremum() < mRows[rowNumber].mName->assignment() )
            {
                conflicts.push_back( std::set< const Bound<T>* >() );
                conflicts.back().insert( mRows[rowNumber].mName->pSupremum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( mRows[rowNumber].mStartEntry, mpEntries );
                while( true )
                {
                    if( (*rowIter).content().isNegative() )
                    {
                        if( mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment() )
                        {
                            // Not a conflict.
                            conflicts.pop_back();
                            break;
                        }
                        else
                        {
                            conflicts.back().insert( mColumns[(*rowIter).columnNumber()].mName->pSupremum() );
                        }
                    }
                    else
                    {
                        if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment() )
                        {
                            // Not a conflict.
                            conflicts.pop_back();
                            break;
                        }
                        else
                        {
                            conflicts.back().insert( mColumns[(*rowIter).columnNumber()].mName->pInfimum() );
                        }
                    }
                    if( rowIter.rowEnd() )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.right();
                    }
                }
            }
            // Lower bound is violated
            else if( mRows[rowNumber].mName->infimum() > mRows[rowNumber].mName->assignment() )
            {
                conflicts.push_back( std::set< const Bound<T>* >() );
                conflicts.back().insert( mRows[rowNumber].mName->pInfimum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( mRows[rowNumber].mStartEntry, mpEntries );
                while( true )
                {
                    if( (*rowIter).content().isPositive() )
                    {
                        if( mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment()  )
                        {
                            // Not a conflict.
                            conflicts.pop_back();
                            break;
                        }
                        else
                        {
                            conflicts.back().insert( mColumns[(*rowIter).columnNumber()].mName->pSupremum() );
                        }
                    }
                    else
                    {
                        if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment()  )
                        {
                            // Not a conflict.
                            conflicts.pop_back();
                            break;
                        }
                        else
                        {
                            conflicts.back().insert( mColumns[(*rowIter).columnNumber()].mName->pInfimum() );
                        }
                    }
                    if( rowIter.rowEnd() )
                    {
                        break;
                    }
                    else
                    {
                        rowIter.right();
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
    template<class T>
    void Tableau<T>::updateBasicAssignments( unsigned _column, const Value<T>& _change )
    {
        if( mColumns[_column].mSize > 0 )
        {
            Iterator columnIter = Iterator( mColumns[_column].mStartEntry, mpEntries );
            while( true )
            {
                Variable<T>& basic = *mRows[(*columnIter).rowNumber()].mName;
                basic.rAssignment() += (_change * (*columnIter).content());
                if( columnIter.columnBegin() )
                {
                    break;
                }
                else
                {
                    columnIter.up();
                }
            }
        }
    }

    /**
     *
     * @param _pivotingElement
     */
    template<class T>
    void Tableau<T>::pivot( EntryID _pivotingElement )
    {
        // TODO: refine the pivoting row
        // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
        // First the column with ** left to the pivoting column until the leftmost column with **.
        std::vector<Iterator> pivotingRowLeftSide = std::vector<Iterator>();
        TableauEntry<T>& pivotEntry = (*mpEntries)[_pivotingElement];
        T& pivotContent = pivotEntry.rContent();
        Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowBegin() )
        {
            iterTemp.left();
            (*iterTemp).rContent() /= -pivotContent; // Division
            pivotingRowLeftSide.push_back( iterTemp );
        }
        // Then the column with ** right to the pivoting column until the rightmost column with **.
        std::vector<Iterator> pivotingRowRightSide = std::vector<Iterator>();
        iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowEnd() )
        {
            iterTemp.right();
            (*iterTemp).rContent() /= -pivotContent; // Division
            pivotingRowRightSide.push_back( iterTemp );
        }

        TableauHead& rowHead = mRows[pivotEntry.rowNumber()];
        TableauHead& columnHead = mColumns[pivotEntry.columnNumber()];
        Variable<T>* nameTmp = rowHead.mName;
        // Update the assignments of the pivoting variables
        nameTmp->rAssignment() += (*mpTheta) * pivotContent;
        columnHead.mName->rAssignment() += (*mpTheta);
        // Swap the row and the column head.
        rowHead.mName = columnHead.mName;
        columnHead.mName = nameTmp;
        unsigned activityTmp = rowHead.mActivity;
        rowHead.mActivity = columnHead.mActivity;
        if( activityTmp == 0 && rowHead.mActivity > 0 )
        {
            mActiveRows.insert( pivotEntry.rowNumber() );
        }
        else if( activityTmp > 0 && rowHead.mActivity == 0 )
        {
            mActiveRows.erase( pivotEntry.rowNumber() );
        }
        columnHead.mActivity = activityTmp;
        // Adapt both variables.
        Variable<T>& basicVar = *rowHead.mName;
        basicVar.rPosition() = pivotEntry.rowNumber();
        basicVar.setBasic( true );
        Variable<T>& nonbasicVar = *columnHead.mName;
        nonbasicVar.rPosition() = pivotEntry.columnNumber();
        nonbasicVar.setBasic( false );
        // Update the content of the pivoting entry
        pivotContent = T(1)/pivotContent; // Division
        #ifdef TLRA_REFINEMENT
        rowRefinement( rowHead );
        #endif
        // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
        // For all rows R having a nonzero entry in the pivoting column:
        //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
        //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
        if( pivotEntry.up() == 0 )
        {
            updateDownwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        else if( pivotEntry.down() == 0 )
        {
            updateUpwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        else
        {
            updateDownwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
            updateUpwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        ++mPivotingSteps;
    }

    /**
     *
     * @param _pivotingElement
     * @param _pivotingRow
     */
    template<class T>
    void Tableau<T>::updateDownwards( EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide )
    {
        std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
        std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
        Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
        while( true )
        {
            // TODO: exclude not activated rows and update them when they get activated
            if( !pivotingColumnIter.columnEnd() )
            {
                pivotingColumnIter.down();
            }
            else
            {
                break;
            }
            // Update the assignment of the basic variable corresponding to this row
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
            // Update the row
            Iterator currentRowIter = pivotingColumnIter;
            auto pivotingRowIter = _pivotingRowLeftSide.begin();
            for( auto currentColumnIter = leftColumnIters.begin(); currentColumnIter != leftColumnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRowLeftSide.end() );
                while( !(*currentColumnIter).columnEnd() && (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).down();
                }
                while( !currentRowIter.rowBegin() && (*currentRowIter).columnNumber() > (**currentColumnIter).columnNumber() )
                {
                    currentRowIter.left();
                }
                // Update the entry
                if( (*currentColumnIter) == currentRowIter )
                {
                    // Entry already exists, so update it only and maybe remove it.
                    T& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                    if( currentRowContent == 0 )
                    {
                        EntryID toRemove = currentRowIter.entryID();
                        (*currentColumnIter).up();
                        currentRowIter.right();
                        removeEntry( toRemove );
                    }
                }
                else
                {
                    EntryID entryID = newTableauEntry();
                    TableauEntry<T>& entry = (*mpEntries)[entryID];
                    // Set the position.
                    entry.setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    entry.setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID upperEntryID = (**currentColumnIter).up();
                        if( upperEntryID != 0 )
                        {
                            (*mpEntries)[upperEntryID].setDown( entryID );
                        }
                        (**currentColumnIter).setUp( entryID );
                        entry.setUp( upperEntryID );
                        entry.setDown( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the lowest in this column.
                        (**currentColumnIter).setDown( entryID );
                        entry.setUp( (*currentColumnIter).entryID() );
                        entry.setDown( 0 );
                        mColumns[entry.columnNumber()].mStartEntry = entryID;
                    }
                    if( (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
                    {
                        // Entry horizontally between two entries.
                        EntryID rightEntryID = (*currentRowIter).right();
                        if( rightEntryID != 0 )
                        {
                            (*mpEntries)[rightEntryID].setLeft( entryID );
                        }
                        (*currentRowIter).setRight( entryID );
                        entry.setRight( rightEntryID );
                        entry.setLeft( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the leftmost in this row.
                        (*currentRowIter).setLeft( entryID );
                        entry.setRight( currentRowIter.entryID() );
                        entry.setLeft( 0 );
                        mRows[entry.rowNumber()].mStartEntry = entryID;
                    }
                    // Set the content of the entry.
                    ++mRows[entry.rowNumber()].mSize;
                    ++mColumns[entry.columnNumber()].mSize;
                    entry.rContent() = (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            currentRowIter = pivotingColumnIter;
            pivotingRowIter = _pivotingRowRightSide.begin();
            for( auto currentColumnIter = rightColumnIters.begin(); currentColumnIter != rightColumnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRowRightSide.end() );
                while( !(*currentColumnIter).columnEnd() && (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).down();
                }
                while( !currentRowIter.rowEnd() && (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
                {
                    currentRowIter.right();
                }
                // Update the entry
                if( (*currentColumnIter) == currentRowIter )
                {
                    // Entry already exists, so update it only and maybe remove it.
                    T& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                    if( currentRowContent == 0 )
                    {
                        EntryID toRemove = currentRowIter.entryID();
                        (*currentColumnIter).up();
                        currentRowIter.left();
                        removeEntry( toRemove );
                    }
                }
                else
                {
                    EntryID entryID = newTableauEntry();
                    TableauEntry<T>& entry = (*mpEntries)[entryID];
                    // Set the position.
                    entry.setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    entry.setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID upperEntryID = (**currentColumnIter).up();
                        if( upperEntryID != 0 )
                        {
                            (*mpEntries)[upperEntryID].setDown( entryID );
                        }
                        (**currentColumnIter).setUp( entryID );
                        entry.setUp( upperEntryID );
                        entry.setDown( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the lowest in this column.
                        (**currentColumnIter).setDown( entryID );
                        entry.setUp( (*currentColumnIter).entryID() );
                        entry.setDown( 0 );
                        mColumns[entry.columnNumber()].mStartEntry = entryID;
                    }
                    if( (*currentRowIter).columnNumber() > (**currentColumnIter).columnNumber() )
                    {
                        // Entry horizontally between two entries.
                        EntryID leftEntryID = (*currentRowIter).left();
                        if( leftEntryID != 0 )
                        {
                            (*mpEntries)[leftEntryID].setRight( entryID );
                        }
                        (*currentRowIter).setLeft( entryID );
                        entry.setLeft( leftEntryID );
                        entry.setRight( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the rightmost in this row.
                        (*currentRowIter).setRight( entryID );
                        entry.setLeft( currentRowIter.entryID() );
                        entry.setRight( 0 );
                    }
                    // Set the content of the entry.
                    ++mRows[entry.rowNumber()].mSize;
                    ++mColumns[entry.columnNumber()].mSize;
                    entry.rContent() = (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() *= (*mpEntries)[_pivotingElement].content();
            #ifdef TLRA_REFINEMENT
            rowRefinement( mRows[(*pivotingColumnIter).rowNumber()] );
            #endif
        }
    }

    /**
     *
     * @param _pivotingElement
     * @param _pivotingRow
     */
    template<class T>
    void Tableau<T>::updateUpwards( EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide )
    {
        std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
        std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
        Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
        while( true )
        {
            // TODO: exclude not activated rows and update them when they get activated
            if( !pivotingColumnIter.columnBegin() )
            {
                pivotingColumnIter.up();
            }
            else
            {
                break;
            }
            // Update the assignment of the basic variable corresponding to this row
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
            // Update the row
            Iterator currentRowIter = pivotingColumnIter;
            auto pivotingRowIter = _pivotingRowLeftSide.begin();
            for( auto currentColumnIter = leftColumnIters.begin(); currentColumnIter != leftColumnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRowLeftSide.end() );
                while( !(*currentColumnIter).columnBegin() && (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).up();
                }
                while( !currentRowIter.rowBegin() && (*currentRowIter).columnNumber() > (**currentColumnIter).columnNumber() )
                {
                    currentRowIter.left();
                }
                // Update the entry
                if( (*currentColumnIter) == currentRowIter )
                {
                    // Entry already exists, so update it only and maybe remove it.
                    T& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                    if( currentRowContent == 0 )
                    {
                        EntryID toRemove = currentRowIter.entryID();
                        (*currentColumnIter).down();
                        currentRowIter.right();
                        removeEntry( toRemove );
                    }
                }
                else
                {
                    EntryID entryID = newTableauEntry();
                    TableauEntry<T>& entry = (*mpEntries)[entryID];
                    // Set the position.
                    entry.setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    entry.setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID lowerEntryID = (**currentColumnIter).down();
                        if( lowerEntryID != 0 )
                        {
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                        }
                        (**currentColumnIter).setDown( entryID );
                        entry.setDown( lowerEntryID );
                        entry.setUp( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        (**currentColumnIter).setUp( entryID );
                        entry.setDown( (*currentColumnIter).entryID() );
                        entry.setUp( 0 );
                    }
                    if( (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
                    {
                        // Entry horizontally between two entries.
                        EntryID rightEntryID = (*currentRowIter).right();
                        if( rightEntryID != 0 )
                        {
                            (*mpEntries)[rightEntryID].setLeft( entryID );
                        }
                        (*currentRowIter).setRight( entryID );
                        entry.setRight( rightEntryID );
                        entry.setLeft( currentRowIter.entryID() );
                    }
                    else
                    {
                        (*currentRowIter).setLeft( entryID );
                        entry.setRight( currentRowIter.entryID() );
                        entry.setLeft( 0 );
                        mRows[entry.rowNumber()].mStartEntry = entryID;
                    }
                    // Set the content of the entry.
                    ++mRows[entry.rowNumber()].mSize;
                    ++mColumns[entry.columnNumber()].mSize;
                    entry.rContent() = (*pivotingColumnIter).content() * (**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            currentRowIter = pivotingColumnIter;
            pivotingRowIter = _pivotingRowRightSide.begin();
            for( auto currentColumnIter = rightColumnIters.begin(); currentColumnIter != rightColumnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRowRightSide.end() );
                while( !(*currentColumnIter).columnBegin() && (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).up();
                }
                while( !currentRowIter.rowEnd() && (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
                {
                    currentRowIter.right();
                }
                // Update the entry
                if( (*currentColumnIter) == currentRowIter )
                {
                    // Entry already exists, so update it only and maybe remove it.
                    T& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    if( currentRowContent == 0 )
                    {
                        EntryID toRemove = currentRowIter.entryID();
                        (*currentColumnIter).down();
                        currentRowIter.left();
                        removeEntry( toRemove );
                    }
                }
                else
                {
                    EntryID entryID = newTableauEntry();
                    TableauEntry<T>& entry = (*mpEntries)[entryID];
                    // Set the position.
                    entry.setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    entry.setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID lowerEntryID = (**currentColumnIter).down();
                        if( lowerEntryID != 0 )
                        {
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                        }
                        (**currentColumnIter).setDown( entryID );
                        entry.setDown( lowerEntryID );
                        entry.setUp( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the uppermost in this column.
                        (**currentColumnIter).setUp( entryID );
                        entry.setDown( (*currentColumnIter).entryID() );
                        entry.setUp( 0 );
                    }
                    if( (*currentRowIter).columnNumber() > (**currentColumnIter).columnNumber() )
                    {
                        // Entry horizontally between two entries.
                        EntryID leftEntryID = (*currentRowIter).left();
                        if( leftEntryID != 0 )
                        {
                            (*mpEntries)[leftEntryID].setRight( entryID );
                        }
                        (*currentRowIter).setLeft( entryID );
                        entry.setLeft( leftEntryID );
                        entry.setRight( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the rightmost in this row.
                        (*currentRowIter).setRight( entryID );
                        entry.setLeft( currentRowIter.entryID() );
                        entry.setRight( 0 );
                    }
                    // Set the content of the entry.
                    ++mRows[entry.rowNumber()].mSize;
                    ++mColumns[entry.columnNumber()].mSize;
                    entry.rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() *= (*mpEntries)[_pivotingElement].content();
            #ifdef TLRA_REFINEMENT
            rowRefinement( mRows[(*pivotingColumnIter).rowNumber()] );
            #endif
        }
    }

    #ifdef TLRA_REFINEMENT
    template<class T>
    void Tableau<T>::rowRefinement( const TableauHead& _row )
    {
        /*
         * Collect the bounds which form an upper resp. lower refinement.
         */
        std::vector<const Bound<T>*>* uPremise = new std::vector<const Bound<T>*>();
        std::vector<const Bound<T>*>* lPremise = new std::vector<const Bound<T>*>();
        Iterator rowEntry = Iterator( _row.mStartEntry, mpEntries );
        while( true )
        {
            if( (*rowEntry).content().isPositive() )
            {
                if( uPremise != NULL )
                {
                    const Bound<T>* sup = mColumns[(*rowEntry).columnNumber()].mName->pSupremum();
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
                    const Bound<T>* inf = mColumns[(*rowEntry).columnNumber()].mName->pInfimum();
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
                    const Bound<T>* inf = mColumns[(*rowEntry).columnNumber()].mName->pInfimum();
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
                    const Bound<T>* sup = mColumns[(*rowEntry).columnNumber()].mName->pSupremum();
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
            if( rowEntry.rowEnd() ) break;
            else rowEntry.right();
        }
        if( uPremise != NULL )
        {
            /*
             * Found an upper refinement.
             */
            Value<T>* newlimit = new Value<T>();
            class std::vector< const Bound<T>* >::iterator bound = uPremise->begin();
            Iterator rowEntry = Iterator( _row.mStartEntry, mpEntries );
            while( true )
            {
                *newlimit += (*bound)->limit() * (*rowEntry).content();
                ++bound;
                if( !rowEntry.rowEnd() ) rowEntry.right();
                else break;
            }
            /*
             * Learn that the strongest weaker upper bound should be activated.
             */
            Variable<T>& bvar = *_row.mName;
            const class Bound<T>::BoundSet& upperBounds = bvar.upperbounds();
            auto ubound = upperBounds.begin();
            while( ubound != upperBounds.end() )
            {
                if( **ubound > *newlimit && (*ubound)->type() != Bound<T>::EQUAL && !(*ubound)->deduced() )
                {
                    break;
                }
                if( *ubound == bvar.pSupremum() )
                {
                    delete newlimit;
                    delete uPremise;
                    goto CheckLowerPremise;
                }
                ++ubound;
            }
            if( ubound != --upperBounds.end() )
            {
                assert( (*ubound)->type() != Bound::EQUAL );
                LearnedBound learnedBound = LearnedBound();
                learnedBound.nextWeakerBound = *ubound;
                learnedBound.premise = uPremise;
                #ifdef TLRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() < (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                {
                    GiNaC::ex lhs = (*ubound)->variable().expression() - newlimit->mainPart();
                    smtrat::Constraint_Relation rel = newlimit->deltaPart() != 0 ? smtrat::CR_LESS : smtrat::CR_LEQ;
                    const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel, (*ubound)->pAsConstraint()->variables() );
                    learnedBound.newBound = bvar.addUpperBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                }
                else
                {
                    learnedBound.newBound = NULL;
                }
                #else
                delete newlimit;
                learnedBound.newBound = NULL;
                #endif
                mLearnedBounds.push_back( learnedBound );
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
            Value<T>* newlimit = new Value<T>();
            class std::vector< const Bound<T>* >::iterator bound = lPremise->begin();
            Iterator rowEntry = Iterator( _row.mStartEntry, mpEntries );
            while( true )
            {
                *newlimit += (*bound)->limit() * (*rowEntry).content();
                ++bound;
                if( !rowEntry.rowEnd() ) rowEntry.right();
                else break;
            }
            /*
             * Learn that the strongest weaker lower bound should be activated.
             */
            Variable<T>& bvar = *_row.mName;
            const class Bound<T>::BoundSet& lowerBounds = bvar.lowerbounds();
            auto lbound = lowerBounds.rbegin();
            while( lbound != lowerBounds.rend() )
            {
                if( **lbound < *newlimit && (*lbound)->type() != Bound<T>::EQUAL && !(*lbound)->deduced() )
                {
                    break;
                }
                if( *lbound == bvar.pInfimum()  )
                {
                    delete newlimit;
                    delete lPremise;
                    return;
                }
                ++lbound;
            }
            if( lbound != --lowerBounds.rend() )
            {
                assert( (*lbound)->type() != Bound::EQUAL );
                LearnedBound learnedBound = LearnedBound();
                learnedBound.nextWeakerBound = *lbound;
                learnedBound.premise = lPremise;
                #ifdef TLRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                {
                    GiNaC::ex lhs = (*lbound)->variable().expression() - newlimit->mainPart();
                    smtrat::Constraint_Relation rel = newlimit->deltaPart() != 0 ? smtrat::CR_GREATER : smtrat::CR_GEQ;
                    const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel, (*lbound)->pAsConstraint()->variables() );
                    learnedBound.newBound = bvar.addLowerBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                }
                else
                {
                    learnedBound.newBound = NULL;
                }
                #else
                delete newlimit;
                learnedBound.newBound = NULL;
                #endif
                mLearnedBounds.push_back( learnedBound );
            }
            else
            {
                delete newlimit;
                delete lPremise;
            }
        }
    }

    template<class T>
    void Tableau<T>::columnRefinement( const TableauHead& _column )
    {
        /*
         * Collect the bounds which form an upper resp. lower refinement.
         */
        std::vector<const Bound<T>*>* uPremise = new std::vector<const Bound<T>*>();
        std::vector<const Bound<T>*>* lPremise = new std::vector<const Bound<T>*>();
        Iterator columnEntry = Iterator( _column.mStartEntry, mpEntries );
        while( true )
        {
            if( (*columnEntry).content().isPositive() )
            {
                if( uPremise != NULL )
                {
                    const Bound<T>* sup = mColumns[(*columnEntry).columnNumber()].mName->pSupremum();
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
                    const Bound<T>* inf = mColumns[(*columnEntry).columnNumber()].mName->pInfimum();
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
                    const Bound<T>* inf = mColumns[(*columnEntry).columnNumber()].mName->pInfimum();
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
                    const Bound<T>* sup = mColumns[(*columnEntry).columnNumber()].mName->pSupremum();
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
            if( columnEntry.columnBegin() ) break;
            else columnEntry.up();
        }
        if( uPremise != NULL )
        {
            /*
             * Found an upper refinement.
             */
            Value<T>* newlimit = new Value<T>();
            class std::vector< const Bound<T>* >::iterator bound = uPremise->begin();
            Iterator columnEntry = Iterator( _column.mStartEntry, mpEntries );
            while( true )
            {
                *newlimit += (*bound)->limit() * (*columnEntry).content();
                ++bound;
                if( !columnEntry.columnBegin() ) columnEntry.up();
                else break;
            }
            /*
             * Learn that the strongest weaker upper bound should be activated.
             */
            Variable<T>& bvar = *_column.mName;
            const class Bound<T>::BoundSet& upperBounds = bvar.upperbounds();
            auto ubound = upperBounds.begin();
            while( ubound != upperBounds.end() )
            {
                if( **ubound > *newlimit && (*ubound)->type() != Bound<T>::EQUAL && !(*ubound)->deduced() )
                {
                    break;
                }
                if( *ubound == bvar.pSupremum() )
                {
                    delete newlimit;
                    delete uPremise;
                    goto CheckLowerPremise;
                }
                ++ubound;
            }
            if( ubound != --upperBounds.end() )
            {
                assert( (*ubound)->type() != Bound::EQUAL );
                LearnedBound learnedBound = LearnedBound();
                learnedBound.nextWeakerBound = *ubound;
                learnedBound.premise = uPremise;
                #ifdef TLRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() < (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                {
                    GiNaC::ex lhs = (*ubound)->variable().expression() - newlimit->mainPart();
                    smtrat::Constraint_Relation rel = newlimit->deltaPart() != 0 ? smtrat::CR_LESS : smtrat::CR_LEQ;
                    const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel, (*ubound)->pAsConstraint()->variables() );
                    learnedBound.newBound = bvar.addUpperBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                }
                else
                {
                    learnedBound.newBound = NULL;
                }
                #else
                delete newlimit;
                learnedBound.newBound = NULL;
                #endif
                mLearnedBounds.push_back( learnedBound );
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
            Value<T>* newlimit = new Value<T>();
            class std::vector< const Bound<T>* >::iterator bound = lPremise->begin();
            Iterator columnEntry = Iterator( _column.mStartEntry, mpEntries );
            while( true )
            {
                *newlimit += (*bound)->limit() * (*columnEntry).content();
                ++bound;
                if( !columnEntry.columnBegin() ) columnEntry.up();
                else break;
            }
            /*
             * Learn that the strongest weaker lower bound should be activated.
             */
            Variable<T>& bvar = *_column.mName;
            const class Bound<T>::BoundSet& lowerBounds = bvar.lowerbounds();
            auto lbound = lowerBounds.rbegin();
            while( lbound != lowerBounds.rend() )
            {
                if( **lbound < *newlimit && (*lbound)->type() != Bound<T>::EQUAL && !(*lbound)->deduced() )
                {
                    break;
                }
                if( *lbound == bvar.pInfimum()  )
                {
                    delete newlimit;
                    delete lPremise;
                    return;
                }
                ++lbound;
            }
            if( lbound != --lowerBounds.rend() )
            {
                assert( (*lbound)->type() != Bound::EQUAL );
                LearnedBound learnedBound = LearnedBound();
                learnedBound.nextWeakerBound = *lbound;
                learnedBound.premise = lPremise;
                #ifdef TLRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                {
                    GiNaC::ex lhs = (*lbound)->variable().expression() - newlimit->mainPart();
                    smtrat::Constraint_Relation rel = newlimit->deltaPart() != 0 ? smtrat::CR_GREATER : smtrat::CR_GEQ;
                    const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel, (*lbound)->pAsConstraint()->variables() );
                    learnedBound.newBound = bvar.addLowerBound( newlimit, mDefaultBoundPosition, constraint, true ).first;
                }
                else
                {
                    learnedBound.newBound = NULL;
                }
                #else
                delete newlimit;
                learnedBound.newBound = NULL;
                #endif
                mLearnedBounds.push_back( learnedBound );
            }
            else
            {
                delete newlimit;
                delete lPremise;
            }
        }
    }

    /**
     *
     */
    template<class T>
    void Tableau<T>::exhaustiveRefinement()
    {
        // TODO: Make this always terminating.
        std::set< unsigned > rowsToRefine = std::set< unsigned >();
        for( unsigned pos = 0; pos < mRows.size(); ++pos )
        {
            rowsToRefine.insert( pos );
        }
        std::set< unsigned > columnsToRefine = std::set< unsigned >();
        for( unsigned pos = 0; pos < mColumns.size(); ++pos )
        {
            columnsToRefine.insert( pos );
        }
        unsigned learnedBoundsSizeBefore = mLearnedBounds.size();
        while( !rowsToRefine.empty() || !columnsToRefine.empty() )
        {
            /*
             * Refine all remaining rows.
             */
            for( auto rowPosition = rowsToRefine.begin(); rowPosition != rowsToRefine.end(); ++rowPosition )
            {
                rowRefinement( mRows[*rowPosition] );
                if( learnedBoundsSizeBefore < mLearnedBounds.size() )
                {
                    /*
                     * If refinement took place, refine all columns where this row has a non zero entry.
                     */
                    Iterator rowEntry = Iterator( mRows[*rowPosition].mStartEntry, mpEntries );
                    while( true )
                    {
                        columnsToRefine.insert( (*rowEntry).columnNumber() );
                        if( !rowEntry.rowEnd() ) rowEntry.right();
                        else break;
                    }
                    learnedBoundsSizeBefore = mLearnedBounds.size();
                }
            }
            rowsToRefine.clear();
            /*
             * Refine all remaining columns.
             */
            for( auto columnPosition = columnsToRefine.begin(); columnPosition != columnsToRefine.end(); ++columnPosition )
            {
                if( learnedBoundsSizeBefore < mLearnedBounds.size() )
                {
                    /*
                     * If refinement took place, refine all rows where this column has a non zero entry.
                     */
                    Iterator columnEntry = Iterator( mColumns[*columnPosition].mStartEntry, mpEntries );
                    while( true )
                    {
                        rowsToRefine.insert( (*columnEntry).rowNumber() );
                        if( !columnEntry.columnBegin() ) columnEntry.up();
                        else break;
                    }
                    learnedBoundsSizeBefore = mLearnedBounds.size();
                }
                columnRefinement( mColumns[*columnPosition] );
            }
            columnsToRefine.clear();
        }
    }
    #endif

    /**
     *
     * @return
     */
    template<class T>
    unsigned Tableau<T>::checkCorrectness() const
    {
        unsigned rowNumber = 0;
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
    template<class T>
    bool Tableau<T>::rowCorrect( unsigned _rowNumber ) const
    {
        GiNaC::ex sumOfNonbasics = *mRows[_rowNumber].mName->pExpression();
        Iterator rowEntry = Iterator( mRows[_rowNumber].mStartEntry, mpEntries );
        while( !rowEntry.rowEnd() )
        {
            sumOfNonbasics -= (*mColumns[(*rowEntry).columnNumber()].mName->pExpression()) * (*rowEntry).content();
            rowEntry.right();
        }
        sumOfNonbasics -= (*mColumns[(*rowEntry).columnNumber()].mName->pExpression()) * (*rowEntry).content();
        sumOfNonbasics = sumOfNonbasics.expand();
        if( sumOfNonbasics != 0 ) return false;
        return true;
    }

    /**
     *
     * @param _out
     * @param _maxEntryLength
     * @param _init
     */
    template<class T>
    void Tableau<T>::printHeap( std::ostream& _out, unsigned _maxEntryLength, const std::string _init ) const
    {
        for( EntryID pos = 0; pos < mpEntries->size(); ++pos )
        {
            std::cout << _init;
            printEntry( _out, pos, _maxEntryLength );
            _out << std::endl;
        }
    }

    /**
     *
     * @param _out
     * @param _entry
     * @param _maxEntryLength
     */
    template<class T>
    void Tableau<T>::printEntry( std::ostream& _out, EntryID _entry, unsigned _maxEntryLength ) const
    {
        _out << std::setw( 4 ) << _entry << ": ";
        std::stringstream out;
        if( _entry > 0 )
        {
            out << (*mpEntries)[_entry].content();
            _out << std::setw( _maxEntryLength ) << out.str();
        }
        else
        {
            _out << std::setw( _maxEntryLength ) << "NULL";
        }
        _out << " at (";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].rowNumber();
        _out << ",";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].columnNumber();
        _out << ") [up:";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].up();
        _out << ", down:";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].down();
        _out << ", left:";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].left();
        _out << ", right:";
        _out << std::setw( 4 ) << (*mpEntries)[_entry].right();
        _out << "]";
    }

    /**
     *
     * @param _out
     * @param _init
     */
    template<class T>
    void Tableau<T>::printVariables( std::ostream& _out, const std::string _init ) const
    {
        _out << _init << "Basic variables:" << std::endl;
        for( class std::vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
            _out << _init << "  ";
            row->mName->print( _out );
            _out << "(" << row->mActivity << ")" << std::endl;
            row->mName->printAllBounds( _out, _init + "                    " );
        }
        _out << _init << "Nonbasic variables:" << std::endl;
        for( class std::vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            _out << _init << "  ";
            column->mName->print( _out );
            _out << "(" << column->mActivity << ")" << std::endl;
            column->mName->printAllBounds( _out, _init + "                    " );
        }
    }

    /**
     *
     * @param _out
     * @param _init
     */
    template<class T>
    void Tableau<T>::printLearnedBounds( const std::string _init, std::ostream& _out  ) const
    {
        for( auto learnedBound = mLearnedBounds.begin(); learnedBound != mLearnedBounds.end(); ++learnedBound )
        {
            for( auto premiseBound = learnedBound->premise->begin(); premiseBound != learnedBound->premise->end(); ++premiseBound )
            {
                _out << _init;
                _out << *(*premiseBound)->variable().pExpression();
                (*premiseBound)->print( true, _out, true );
                _out << std::endl;
            }
            _out << _init << "               | " << std::endl;
            _out << _init << "               V " << std::endl;
            _out << _init << *learnedBound->nextWeakerBound->variable().pExpression();
            learnedBound->nextWeakerBound->print( true, _out, true );
            _out << std::endl;
            _out << _init << *learnedBound->nextWeakerBound->variable().pExpression();
            learnedBound->newBound->print( true, _out, true );
            _out << std::endl << std::endl;
        }
    }

    /**
     *
     * @param _out
     * @param _maxEntryLength
     * @param _init
     */
    template<class T>
    void Tableau<T>::print( std::ostream& _out, unsigned _maxEntryLength, const std::string _init ) const
    {
        char     frameSign     = '-';
        _out << _init << std::setw( _maxEntryLength * (mWidth + 1) ) << std::setfill( frameSign ) << "" << std::endl;
        _out << _init << std::setw( _maxEntryLength ) << std::setfill( ' ' ) << "#";
        for( class std::vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            std::stringstream out;
            out << *column->mName->pExpression();
            _out << std::setw( _maxEntryLength ) << out.str() + " #";
        }
        _out << std::endl;
        _out << _init << std::setw( _maxEntryLength * (mWidth + 1) ) << std::setfill( '#' ) << "" << std::endl;
        _out << std::setfill( ' ' );
        for( class std::vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
            _out << _init;
            std::stringstream out;
            out << *row->mName->pExpression();
            _out << std::setw( _maxEntryLength ) << out.str() + " #";
            Iterator rowIter = Iterator( row->mStartEntry, mpEntries );
            unsigned currentColumn = 0;
            while( true )
            {
                for( unsigned i = currentColumn; i < (*rowIter).columnNumber(); ++i )
                {
                    _out << std::setw( _maxEntryLength ) << "0 #";
                }
                std::stringstream out;
                out << (*rowIter).content();
                _out << std::setw( _maxEntryLength ) << out.str() + " #";
                currentColumn = (*rowIter).columnNumber()+1;
                if( rowIter.rowEnd() )
                {
                    for( unsigned i = currentColumn; i < mWidth; ++i )
                    {
                        _out << std::setw( _maxEntryLength ) << "0 #";
                    }
                    _out << std::endl;
                    break;
                }
                rowIter.right();
            }
        }
        _out << _init << std::setw( _maxEntryLength * (mWidth + 1) ) << std::setfill( frameSign ) << "" << std::endl;
        _out << std::setfill( ' ' );
    }
}    // end namspace tlra

#endif   /* TLRA_TABLEAU_H */
