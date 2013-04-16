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
 * @file Tableau.cpp
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#include <sstream>

#include "Tableau.h"
#include "LRAModule.h"

using namespace std;
using namespace GiNaC;

//#define LRA_PRINT_STATS
//#define LRA_USE_OCCURENCE_STRATEGY
#ifndef LRA_USE_OCCURENCE_STRATEGY
#define LRA_USE_THETA_STRATEGY
#endif

// TODO: Update only rows, which correspond to a bounded variable.
//       It needs, that in each entry the non basic (column) variable is stored,
//       in order to update the row belatedly.

namespace lra
{
    Tableau::Tableau( smtrat::Formula::iterator _defaultBoundPosition ):
        mHeight( 0 ),
        mWidth( 0 ),
        mPivotingSteps( 0 ),
        #ifdef LRA_USE_PIVOTING_STRATEGY
        mRestarts( 0 ),
        mNextRestartBegin( 0 ),
        mNextRestartEnd( 0 ),
        #endif
        mDefaultBoundPosition( _defaultBoundPosition ),
        mUnusedIDs(),
        mRows(),
        mColumns(),
        mActiveRows()
        #ifdef LRA_REFINEMENT
        ,
        mLearnedBounds()
        #endif
    {
        mpEntries = new vector< TableauEntry >();
        mpEntries->push_back( TableauEntry() );
        mpTheta = new Value();
    };

    Tableau::~Tableau()
    {
        #ifdef LRA_PRINT_STATS
        cout << "#Pivoting steps:  " << mPivotingSteps << endl;
        cout << "#Tableus entries: " << mpEntries->size()-1 << endl;
        cout << "Tableau coverage: " << (double)(mpEntries->size()-1)/(double)(mRows.size()*mColumns.size())*100 << "%" << endl;
        #endif
        while( !mRows.empty() )
        {
            Variable* varToDel = mRows.back().mName;
            mRows.pop_back();
            delete varToDel;
        }
        while( !mColumns.empty() )
        {
            Variable* varToDel = mColumns.back().mName;
            mColumns.pop_back();
            delete varToDel;
        }
        while( !mUnusedIDs.empty() )
        {
            mUnusedIDs.pop();
        }
        while( !mpEntries->empty() )
        {
            numeric* tmpNum = mpEntries->back().pContent();
            mpEntries->pop_back();
            delete tmpNum;
        }
        delete mpEntries;
        delete mpTheta;
    };

    /**
     *
     * @return
     */
    EntryID Tableau::newTableauEntry()
    {
        if( mUnusedIDs.empty() )
        {
            mpEntries->push_back( TableauEntry( 0, 0, 0, 0, 0, 0, new numeric( 0 ) ) );
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
    void Tableau::removeEntry( EntryID _entryID )
    {
        TableauEntry& entry = (*mpEntries)[_entryID];
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
    Variable* Tableau::newNonbasicVariable( const ex* _ex )
    {
        Variable* var = new Variable( mWidth++, false, _ex, mDefaultBoundPosition );
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
    Variable* Tableau::newBasicVariable( const ex* _ex, const vector< Variable* >& _nonbasicVariables, vector< numeric >& _coefficients )
    {
        assert( _coefficients.size() == _coefficients.size() );
        Variable* var = new Variable( mHeight++, true, _ex, mDefaultBoundPosition );
        mRows.push_back( TableauHead() );
        EntryID currentStartEntryOfRow = 0;
        vector< Variable* >::const_iterator basicVar = _nonbasicVariables.begin();
        vector< numeric >::iterator coeff = _coefficients.begin();
        while( basicVar != _nonbasicVariables.end() )
        {
            EntryID entryID = newTableauEntry();
            TableauEntry& entry = (*mpEntries)[entryID];
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

    #ifdef LRA_USE_PIVOTING_STRATEGY
//    /**
//     *
//     * @param y
//     * @param x
//     * @return
//     */
//    static unsigned luby( unsigned _numberOfRestarts )
//    {
//        // Find the finite subsequence that contains index 'x', and the
//        // size of that subsequence:
//        cout << "_numberOfRestarts = " << _numberOfRestarts;
//        unsigned size, seq;
//        for( size = 1, seq = 0; size < _numberOfRestarts + 1; seq++, size = 2 * size + 1 );
//
//        while( size - 1 != _numberOfRestarts )
//        {
//            size = (size - 1) >> 1;
//            seq--;
//            _numberOfRestarts = _numberOfRestarts % size;
//        }
//        cout << " results in seq = " << seq << endl;
//        if( seq >= 64 ) return 0;
//        cout << " results in seq = " << seq << endl;
//        unsigned result = 1;
//        result = result << seq;
//        cout << "result = " << result << endl;
//        return result;
//    }
    #endif

    /**
     *
     * @return
     */
    pair<EntryID,bool> Tableau::nextPivotingElement()
    {
        #ifdef LRA_USE_PIVOTING_STRATEGY
        //  Dynamic strategy for a fixed number of steps
//        if( mPivotingSteps >= mNextRestartBegin && mPivotingSteps < mNextRestartEnd )
        if( mPivotingSteps < mNextRestartEnd )
        {
            #ifdef LRA_USE_OCCURENCE_STRATEGY
            unsigned smallestRowSize = mWidth;
            unsigned smallestColumnSize = mHeight;
            #endif
            EntryID beginOfBestRow = 0;
            EntryID beginOfFirstConflictRow = 0;
            *mpTheta = Value( 0 );
            for( auto rowNumber = mActiveRows.begin(); rowNumber != mActiveRows.end(); ++rowNumber )
            {
                Value theta = Value();
                pair<EntryID,bool> result = isSuitable( *rowNumber, theta );
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
                    #ifdef LRA_USE_THETA_STRATEGY
                    if( beginOfBestRow == 0 || abs( theta.mainPart() ) > abs( mpTheta->mainPart() ) )
                    {
                        beginOfBestRow = result.first;
                        *mpTheta = theta;
                    }
                    #endif
                    #ifdef LRA_USE_OCCURENCE_STRATEGY
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
                return pair<EntryID,bool>( beginOfFirstConflictRow, false );
            }
            else if( beginOfBestRow != 0 )
            {
                // The best pivoting element found
                return pair<EntryID,bool>( beginOfBestRow, true );
            }
            else
            {
                // Found no pivoting element, that is no variable violates its bounds.
                return pair<EntryID,bool>( 0, true );
            }
        }
        // Bland's rule
        else
        {
//            if( mPivotingSteps == mNextRestartEnd )
//            {
//                mNextRestartBegin = mNextRestartEnd + mWidth * luby( mRestarts++ );
//                mNextRestartEnd = mNextRestartBegin + mWidth;
//                cout << "Next restart range = [" << mNextRestartBegin << "," << mNextRestartEnd << "]" << endl;
//            }
        #endif
            for( auto rowNumber = mActiveRows.begin(); rowNumber != mActiveRows.end(); ++rowNumber )
            {
                pair<EntryID,bool> result = isSuitable( *rowNumber, *mpTheta );
                if( !result.second )
                {
                    // Found a conflicting row.
                    return pair<EntryID,bool>( result.first, false );
                }
                else if( result.first != 0 )
                {
                    // Found a pivoting element
                    return pair<EntryID,bool>( result.first, true );
                }
            }
            // Found no pivoting element, that is no variable violates its bounds.
            return pair<EntryID,bool>( 0, true );
        #ifdef LRA_USE_PIVOTING_STRATEGY
        }
        #endif
    }

    /**
     *
     * @param _rowNumber
     * @return
     */
    pair<EntryID,bool> Tableau::isSuitable( unsigned _rowNumber, Value& _theta ) const
    {
        EntryID bestEntry = 0;
        const TableauHead& _rowHead = mRows[_rowNumber];
        const Variable& basicVar = *_rowHead.mName;
        const Bound& basicVarSupremum = basicVar.supremum();
        const Value& basicVarAssignment = basicVar.assignment();
        const Bound& basicVarInfimum = basicVar.infimum();
        const EntryID& rowStartEntry = _rowHead.mStartEntry;
        // Upper bound is violated
        if( basicVarSupremum < basicVarAssignment )
        {
            // Check all entries in the row / nonbasic variables
            Iterator rowIter = Iterator( rowStartEntry, mpEntries );
            while( true )
            {
                const Variable& nonBasicVar = *mColumns[(*rowIter).columnNumber()].mName;
                if( (*rowIter).content().info( info_flags::negative ) )
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
                        return pair<EntryID,bool>( rowStartEntry, false );
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
                const Variable& nonBasicVar = *mColumns[(*rowIter).columnNumber()].mName;
                if( (*rowIter).content().info( info_flags::positive ) )
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
                        return pair<EntryID,bool>( rowStartEntry, false );
                    }
                    break;
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        return pair<EntryID,bool>( bestEntry, true );
    }

    bool Tableau::betterEntry( EntryID _isBetter, EntryID _than ) const
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
    vector< const Bound* > Tableau::getConflict( EntryID _rowEntry ) const
    {
        assert( _rowEntry != 0 );
        const TableauHead& row = mRows[(*mpEntries)[_rowEntry].rowNumber()];
        // Upper bound is violated
        vector< const Bound* > conflict = vector< const Bound* >();
        if( row.mName->supremum() < row.mName->assignment() )
        {
            conflict.push_back( row.mName->pSupremum() );
            // Check all entries in the row / basic variables
            Iterator rowIter = Iterator( row.mStartEntry, mpEntries );
            while( true )
            {
                if( (*rowIter).content().info( info_flags::negative ) )
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
                if( (*rowIter).content().info( info_flags::positive ) )
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
    vector< set< const Bound* > > Tableau::getConflictsFrom( EntryID _rowEntry ) const
    {
        vector< set< const Bound* > > conflicts = vector< set< const Bound* > >();
        for( unsigned rowNumber = (*mpEntries)[_rowEntry].rowNumber(); rowNumber < mRows.size(); ++rowNumber )
        {
            // Upper bound is violated
            if( mRows[rowNumber].mName->supremum() < mRows[rowNumber].mName->assignment() )
            {
                conflicts.push_back( set< const Bound* >() );
                conflicts.back().insert( mRows[rowNumber].mName->pSupremum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( mRows[rowNumber].mStartEntry, mpEntries );
                while( true )
                {
                    if( (*rowIter).content().info( info_flags::negative ) )
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
                conflicts.push_back( set< const Bound* >() );
                conflicts.back().insert( mRows[rowNumber].mName->pInfimum() );
                // Check all entries in the row / basic variables
                Iterator rowIter = Iterator( mRows[rowNumber].mStartEntry, mpEntries );
                while( true )
                {
                    if( (*rowIter).content().info( info_flags::positive ) )
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
    void Tableau::updateBasicAssignments( unsigned _column, const Value& _change )
    {
        if( mColumns[_column].mSize > 0 )
        {
            Iterator columnIter = Iterator( mColumns[_column].mStartEntry, mpEntries );
            while( true )
            {
                Variable& basic = *mRows[(*columnIter).rowNumber()].mName;
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
    void Tableau::pivot( EntryID _pivotingElement )
    {
        // TODO: refine the pivoting row
        // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
        // First the column with ** left to the pivoting column until the leftmost column with **.
        vector<Iterator> pivotingRowLeftSide = vector<Iterator>();
        TableauEntry& pivotEntry = (*mpEntries)[_pivotingElement];
        numeric& pivotContent = pivotEntry.rContent();
        Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowBegin() )
        {
            iterTemp.left();
            (*iterTemp).rContent() /= -pivotContent;
            pivotingRowLeftSide.push_back( iterTemp );
        }
        // Then the column with ** right to the pivoting column until the rightmost column with **.
        vector<Iterator> pivotingRowRightSide = vector<Iterator>();
        iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowEnd() )
        {
            iterTemp.right();
            (*iterTemp).rContent() /= -pivotContent;
            pivotingRowRightSide.push_back( iterTemp );
        }

        TableauHead& rowHead = mRows[pivotEntry.rowNumber()];
        TableauHead& columnHead = mColumns[pivotEntry.columnNumber()];
        Variable* nameTmp = rowHead.mName;
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
        Variable& basicVar = *rowHead.mName;
        basicVar.rPosition() = pivotEntry.rowNumber();
        basicVar.setBasic( true );
        Variable& nonbasicVar = *columnHead.mName;
        nonbasicVar.rPosition() = pivotEntry.columnNumber();
        nonbasicVar.setBasic( false );
        // Update the content of the pivoting entry
        pivotContent = 1/pivotContent;
        #ifdef LRA_REFINEMENT
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
    void Tableau::updateDownwards( EntryID _pivotingElement, vector<Iterator>& _pivotingRowLeftSide, vector<Iterator>& _pivotingRowRightSide )
    {
        vector<Iterator> leftColumnIters = vector<Iterator>( _pivotingRowLeftSide );
        vector<Iterator> rightColumnIters = vector<Iterator>( _pivotingRowRightSide );
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
            numeric& currentContent = (*pivotingColumnIter).rContent();
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() += (*mpTheta) * currentContent;
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
                    numeric& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += currentContent * (**pivotingRowIter).content();
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
                    TableauEntry& entry = (*mpEntries)[entryID];
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
                    entry.rContent() = currentContent * (**pivotingRowIter).content();
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
                    numeric& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += currentContent * (**pivotingRowIter).content();
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
                    TableauEntry& entry = (*mpEntries)[entryID];
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
                    entry.rContent() = currentContent * (**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            currentContent *= (*mpEntries)[_pivotingElement].content();
            #ifdef LRA_REFINEMENT
            rowRefinement( mRows[(*pivotingColumnIter).rowNumber()] );
            #endif
        }
    }

    /**
     *
     * @param _pivotingElement
     * @param _pivotingRow
     */
    void Tableau::updateUpwards( EntryID _pivotingElement, vector<Iterator>& _pivotingRowLeftSide, vector<Iterator>& _pivotingRowRightSide )
    {
        vector<Iterator> leftColumnIters = vector<Iterator>( _pivotingRowLeftSide );
        vector<Iterator> rightColumnIters = vector<Iterator>( _pivotingRowRightSide );
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
            numeric& currentContent = (*pivotingColumnIter).rContent();
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() += (*mpTheta) * currentContent;
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
                    numeric& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += currentContent * (**pivotingRowIter).content();
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
                    TableauEntry& entry = (*mpEntries)[entryID];
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
                    entry.rContent() = currentContent * (**pivotingRowIter).content();
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
                    numeric& currentRowContent = (*currentRowIter).rContent();
                    currentRowContent += currentContent*(**pivotingRowIter).content();
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
                    TableauEntry& entry = (*mpEntries)[entryID];
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
                    entry.rContent() = currentContent*(**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            currentContent *= (*mpEntries)[_pivotingElement].content();
            #ifdef LRA_REFINEMENT
            rowRefinement( mRows[(*pivotingColumnIter).rowNumber()] );
            #endif
        }
    }

    #ifdef LRA_REFINEMENT
    void Tableau::rowRefinement( const TableauHead& _row )
    {
        /*
         * Collect the bounds which form an upper resp. lower refinement.
         */
        vector<const Bound*>* uPremise = new vector<const Bound*>();
        vector<const Bound*>* lPremise = new vector<const Bound*>();
        Iterator rowEntry = Iterator( _row.mStartEntry, mpEntries );
        while( true )
        {
            if( (*rowEntry).content().is_positive() )
            {
                if( uPremise != NULL )
                {
                    const Bound* sup = mColumns[(*rowEntry).columnNumber()].mName->pSupremum();
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
                    const Bound* inf = mColumns[(*rowEntry).columnNumber()].mName->pInfimum();
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
                    const Bound* inf = mColumns[(*rowEntry).columnNumber()].mName->pInfimum();
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
                    const Bound* sup = mColumns[(*rowEntry).columnNumber()].mName->pSupremum();
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
            Value* newlimit = new Value();
            vector< const Bound* >::iterator bound = uPremise->begin();
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
            Variable& bvar = *_row.mName;
            const BoundSet& upperBounds = bvar.upperbounds();
            auto ubound = upperBounds.begin();
            while( ubound != upperBounds.end() )
            {
                if( **ubound > *newlimit && (*ubound)->type() != Bound::EQUAL && !(*ubound)->deduced() )
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
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() < (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                {
                    ex lhs = (*ubound)->variable().expression() - newlimit->mainPart();
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
            Value* newlimit = new Value();
            vector< const Bound* >::iterator bound = lPremise->begin();
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
            Variable& bvar = *_row.mName;
            const BoundSet& lowerBounds = bvar.lowerbounds();
            auto lbound = lowerBounds.rbegin();
            while( lbound != lowerBounds.rend() )
            {
                if( **lbound < *newlimit && (*lbound)->type() != Bound::EQUAL )
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
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                {
                    ex lhs = (*lbound)->variable().expression() - newlimit->mainPart();
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

    void Tableau::columnRefinement( const TableauHead& _column )
    {
        /*
         * Collect the bounds which form an upper resp. lower refinement.
         */
        vector<const Bound*>* uPremise = new vector<const Bound*>();
        vector<const Bound*>* lPremise = new vector<const Bound*>();
        Iterator columnEntry = Iterator( _column.mStartEntry, mpEntries );
        while( true )
        {
            if( (*columnEntry).content().is_positive() )
            {
                if( uPremise != NULL )
                {
                    const Bound* sup = mColumns[(*columnEntry).columnNumber()].mName->pSupremum();
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
                    const Bound* inf = mColumns[(*columnEntry).columnNumber()].mName->pInfimum();
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
                    const Bound* inf = mColumns[(*columnEntry).columnNumber()].mName->pInfimum();
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
                    const Bound* sup = mColumns[(*columnEntry).columnNumber()].mName->pSupremum();
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
            Value* newlimit = new Value();
            vector< const Bound* >::iterator bound = uPremise->begin();
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
            Variable& bvar = *_column.mName;
            const BoundSet& upperBounds = bvar.upperbounds();
            auto ubound = upperBounds.begin();
            while( ubound != upperBounds.end() )
            {
                if( **ubound > *newlimit && (*ubound)->type() != Bound::EQUAL && !(*ubound)->deduced() )
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
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                lock_guard<recursive_mutex> lock( smtrat::Constraint::mMutex );
                if( newlimit->mainPart() < (*ubound)->limit().mainPart() || (*ubound)->limit().deltaPart() == 0 )
                {
                    ex lhs = (*ubound)->variable().expression() - newlimit->mainPart();
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
            Value* newlimit = new Value();
            vector< const Bound* >::iterator bound = lPremise->begin();
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
            Variable& bvar = *_column.mName;
            const BoundSet& lowerBounds = bvar.lowerbounds();
            auto lbound = lowerBounds.rbegin();
            while( lbound != lowerBounds.rend() )
            {
                if( **lbound < *newlimit && (*lbound)->type() != Bound::EQUAL )
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
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                lock_guard<recursive_mutex> lock( smtrat::Constraint::mMutex );
                if( newlimit->mainPart() > (*lbound)->limit().mainPart() || (*lbound)->limit().deltaPart() == 0 )
                {
                    ex lhs = (*lbound)->variable().expression() - newlimit->mainPart();
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
    void Tableau::exhaustiveRefinement()
    {
        // TODO: Make this always terminating.
        set< unsigned > rowsToRefine = set< unsigned >();
        for( unsigned pos = 0; pos < mRows.size(); ++pos )
        {
            rowsToRefine.insert( pos );
        }
        set< unsigned > columnsToRefine = set< unsigned >();
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
    unsigned Tableau::checkCorrectness() const
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
    bool Tableau::rowCorrect( unsigned _rowNumber ) const
    {
        ex sumOfNonbasics = *mRows[_rowNumber].mName->pExpression();
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
    const smtrat::Constraint* Tableau::gomoryCut(const GiNaC::numeric ass, unsigned row_position, vector<const smtrat::Constraint*>& constr_vec)
    {     
        Iterator row_iterator = Iterator(mRows.at(row_position).mStartEntry, mpEntries);
        vector<GOMORY_SET> splitting = vector<GOMORY_SET>();
        // Check, whether the conditions of a Gomory Cut are satisfied
        while(!row_iterator.rowEnd())
        {  
            const Variable& nonBasicVar = *mColumns[(*row_iterator).columnNumber()].mName;
            if(nonBasicVar.infimum() == nonBasicVar.assignment() ||
               nonBasicVar.supremum() == nonBasicVar.assignment())
            {
                if(nonBasicVar.infimum() == nonBasicVar.assignment())
                {
                    if((*row_iterator).content()<0)
                        splitting.push_back(J_MINUS);
                    else 
                        splitting.push_back(J_PLUS);         
                }
                else
                {
                    if((*row_iterator).content()<0)
                        splitting.push_back(K_MINUS);
                    else 
                        splitting.push_back(K_PLUS);
                }
            }                                 
            else
            {
                return NULL;
            }                               
            row_iterator.right();
        }
        // A Gomory Cut can be constructed              
        vector<numeric> coeffs = vector<numeric>();
        numeric coeff;
        numeric f_zero = ass-numeric(cln::floor1(cln::the<cln::cl_RA>(ass.to_cl_N())));
        ex sum = ex();
        // Construction of the Gomory Cut 
        vector<GOMORY_SET>::const_iterator vec_iter = splitting.begin();
        row_iterator = Iterator(mRows.at(row_position).mStartEntry, mpEntries);
        while(!row_iterator.rowEnd())
        {                 
            const Variable& nonBasicVar = (*mColumns[(*row_iterator).columnNumber()].mName);
            if((*vec_iter)==J_MINUS)
            {
                numeric bound = nonBasicVar.infimum().limit().mainPart();
                coeff = -(*row_iterator).content()/(f_zero);
                constr_vec.push_back(nonBasicVar.infimum().pAsConstraint());                    
                sum += coeff*(nonBasicVar.expression()-bound);                   
            }                 
            else if ((*vec_iter)==J_PLUS)
            {
                numeric bound = nonBasicVar.infimum().limit().mainPart();
                coeff = (*row_iterator).content()/(1-f_zero);
                constr_vec.push_back(nonBasicVar.infimum().pAsConstraint());
                sum += coeff*(nonBasicVar.expression()-bound);                   
            }
            else if ((*vec_iter)==K_MINUS)
            {
                numeric bound = nonBasicVar.supremum().limit().mainPart();
                coeff = -(*row_iterator).content()/(1-f_zero);
                constr_vec.push_back(nonBasicVar.supremum().pAsConstraint());
                sum += coeff*(bound-nonBasicVar.expression());                   
            }
            else if ((*vec_iter)==K_PLUS) 
            {
                numeric bound = nonBasicVar.supremum().limit().mainPart();
                coeff = (*row_iterator).content()/f_zero;
                constr_vec.push_back(nonBasicVar.supremum().pAsConstraint());
                sum += coeff*(bound-nonBasicVar.expression());
            }     
            coeffs.push_back(coeff);
            row_iterator.right();
            ++vec_iter;
        }            
        const smtrat::Constraint* gomory_constr = smtrat::Formula::newConstraint(sum-1,smtrat::CR_GEQ, smtrat::Formula::constraintPool().realVariables());
        ex *psum = new ex(sum-gomory_constr->constantPart());
        Value* bound = new Value( gomory_constr->constantPart() );
        Variable* var = new Variable( mHeight++, true, psum, mDefaultBoundPosition );
        (*var).addLowerBound( bound, mDefaultBoundPosition, gomory_constr );
        vector<numeric>::const_iterator coeffs_iter = coeffs.begin();
        row_iterator = Iterator( mRows.at(row_position).mStartEntry, mpEntries );
        mRows.push_back( TableauHead() );
        EntryID currentStartEntryOfRow = 0;
        EntryID leftID;            
        while(coeffs_iter != coeffs.end())
        {
            const Variable& nonBasicVar = *mColumns[(*row_iterator).columnNumber()].mName;
            EntryID entryID = newTableauEntry();
            TableauEntry& entry = (*mpEntries)[entryID];
            entry.setColumnNumber(nonBasicVar.position());
            entry.setRowNumber(mHeight-1);
            entry.rContent() = *coeffs_iter;
            TableauHead& columnHead = mColumns[entry.columnNumber()];
            EntryID& columnStart = columnHead.mStartEntry;
            (*mpEntries)[columnStart].setDown(entryID);
            entry.setUp(columnStart);                
            columnStart = entryID;
            ++columnHead.mSize;
            if( currentStartEntryOfRow == 0 )
            {
                currentStartEntryOfRow = entryID;
                entry.setLeft(0);
                leftID = entryID;
            }  
            else 
            {
                (*mpEntries)[entryID].setLeft(leftID);
                (*mpEntries)[leftID].setRight(entryID); 
                leftID = entryID;
            }
            ++coeffs_iter;
            row_iterator.right();
        }            
        (*mpEntries)[leftID].setRight(0);
        TableauHead& rowHead = mRows[mHeight-1];
        rowHead.mStartEntry = currentStartEntryOfRow;
        rowHead.mSize = coeffs.size();
        rowHead.mName = var; 
        return gomory_constr;     
    }
    #endif

    /**
     *
     * @param _out
     * @param _maxEntryLength
     * @param _init
     */
    void Tableau::printHeap( ostream& _out, unsigned _maxEntryLength, const string _init ) const
    {
        for( EntryID pos = 0; pos < mpEntries->size(); ++pos )
        {
            cout << _init;
            printEntry( _out, pos, _maxEntryLength );
            _out << endl;
        }
    }

    /**
     *
     * @param _out
     * @param _entry
     * @param _maxEntryLength
     */
    void Tableau::printEntry( ostream& _out, EntryID _entry, unsigned _maxEntryLength ) const
    {
        _out << setw( 4 ) << _entry << ": ";
        stringstream out;
        if( _entry > 0 )
        {
            out << (*mpEntries)[_entry].content();
            _out << setw( _maxEntryLength ) << out.str();
        }
        else
        {
            _out << setw( _maxEntryLength ) << "NULL";
        }
        _out << " at (";
        _out << setw( 4 ) << (*mpEntries)[_entry].rowNumber();
        _out << ",";
        _out << setw( 4 ) << (*mpEntries)[_entry].columnNumber();
        _out << ") [up:";
        _out << setw( 4 ) << (*mpEntries)[_entry].up();
        _out << ", down:";
        _out << setw( 4 ) << (*mpEntries)[_entry].down();
        _out << ", left:";
        _out << setw( 4 ) << (*mpEntries)[_entry].left();
        _out << ", right:";
        _out << setw( 4 ) << (*mpEntries)[_entry].right();
        _out << "]";
    }

    /**
     *
     * @param _out
     * @param _init
     */
    void Tableau::printVariables( ostream& _out, const string _init ) const
    {
        _out << _init << "Basic variables:" << endl;
        for( vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
            _out << _init << "  ";
            row->mName->print( _out );
            _out << "(" << row->mActivity << ")" << endl;
            row->mName->printAllBounds( _out, _init + "                    " );
        }
        _out << _init << "Nonbasic variables:" << endl;
        for( vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            _out << _init << "  ";
            column->mName->print( _out );
            _out << "(" << column->mActivity << ")" << endl;
            column->mName->printAllBounds( _out, _init + "                    " );
        }
    }

    /**
     *
     * @param _out
     * @param _init
     */
    void Tableau::printLearnedBounds( const string _init, ostream& _out  ) const
    {
        for( auto learnedBound = mLearnedBounds.begin(); learnedBound != mLearnedBounds.end(); ++learnedBound )
        {
            for( auto premiseBound = learnedBound->premise->begin(); premiseBound != learnedBound->premise->end(); ++premiseBound )
            {
                _out << _init;
                _out << *(*premiseBound)->variable().pExpression();
                (*premiseBound)->print( true, _out, true );
                _out << endl;
            }
            _out << _init << "               | " << endl;
            _out << _init << "               V " << endl;
            _out << _init << *learnedBound->nextWeakerBound->variable().pExpression();
            learnedBound->nextWeakerBound->print( true, _out, true );
            _out << endl;
            _out << _init << *learnedBound->nextWeakerBound->variable().pExpression();
            learnedBound->newBound->print( true, _out, true );
            _out << endl << endl;
        }
    }

    /**
     *
     * @param _out
     * @param _maxEntryLength
     * @param _init
     */
    void Tableau::print( ostream& _out, unsigned _maxEntryLength, const string _init ) const
    {
        char     frameSign     = '-';
        _out << _init << setw( _maxEntryLength * (mWidth + 1) ) << setfill( frameSign ) << "" << endl;
        _out << _init << setw( _maxEntryLength ) << setfill( ' ' ) << "#";
        for( vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            stringstream out;
            out << *column->mName->pExpression();
            _out << setw( _maxEntryLength ) << out.str() + " #";
        }
        _out << endl;
        _out << _init << setw( _maxEntryLength * (mWidth + 1) ) << setfill( '#' ) << "" << endl;
        _out << setfill( ' ' );
        for( vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
            _out << _init;
            stringstream out;
            out << *row->mName->pExpression();
            _out << setw( _maxEntryLength ) << out.str() + " #";
            Iterator rowIter = Iterator( row->mStartEntry, mpEntries );
            unsigned currentColumn = 0;
            while( true )
            {
                for( unsigned i = currentColumn; i < (*rowIter).columnNumber(); ++i )
                {
                    _out << setw( _maxEntryLength ) << "0 #";
                }
                stringstream out;
                out << (*rowIter).content();
                _out << setw( _maxEntryLength ) << out.str() + " #";
                currentColumn = (*rowIter).columnNumber()+1;
                if( rowIter.rowEnd() )
                {
                    for( unsigned i = currentColumn; i < mWidth; ++i )
                    {
                        _out << setw( _maxEntryLength ) << "0 #";
                    }
                    _out << endl;
                    break;
                }
                rowIter.right();
            }
        }
        _out << _init << setw( _maxEntryLength * (mWidth + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setfill( ' ' );
    }

}  // end namspace lra
