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

using namespace std;
using namespace GiNaC;

namespace lraone
{
    Tableau::Tableau():
        mHeight( 0 ),
        mWidth( 0 ),
        mPivotingSteps( 0 ),
        #ifdef LRA_USE_PIVOTING_STRATEGY
        mRestarts( 0 ),
        mNextRestartBegin( 0 ),
        mNextRestartEnd( 0 ),
        #endif
        mUnusedIDs(),
        mRows(),
        mColumns()
    {
        mpEntries = new vector< TableauEntry >();
        mpEntries->push_back( TableauEntry() );
        mpTheta = new Value();
    };

    Tableau::~Tableau()
    {
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
        if( (*mpEntries)[_entryID].up() != 0 )
        {
            (*mpEntries)[(*mpEntries)[_entryID].up()].setDown( (*mpEntries)[_entryID].down() );
        }
        if( (*mpEntries)[_entryID].down() != 0 )
        {
            (*mpEntries)[(*mpEntries)[_entryID].down()].setUp( (*mpEntries)[_entryID].up() );
        }
        else
        {
            mColumns[(*mpEntries)[_entryID].columnNumber()].mStartEntry = (*mpEntries)[_entryID].up();
        }
        if( (*mpEntries)[_entryID].left() != 0 )
        {
            (*mpEntries)[(*mpEntries)[_entryID].left()].setRight( (*mpEntries)[_entryID].right() );
        }
        else
        {
            mRows[(*mpEntries)[_entryID].rowNumber()].mStartEntry = (*mpEntries)[_entryID].right();
        }
        if( (*mpEntries)[_entryID].right() != 0 )
        {
            (*mpEntries)[(*mpEntries)[_entryID].right()].setLeft( (*mpEntries)[_entryID].left() );
        }
        --mRows[(*mpEntries)[_entryID].rowNumber()].mSize;
        --mColumns[(*mpEntries)[_entryID].columnNumber()].mSize;
        mUnusedIDs.push( _entryID );
    }

    /**
     *
     * @param _ex
     * @return
     */
    Variable* Tableau::newNonbasicVariable( const ex* _ex )
    {
        Variable* var = new Variable( mWidth++, false, _ex );
        #ifdef LRA_USE_PIVOTING_STRATEGY
        ++mNextRestartEnd;
        #endif
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
        Variable* var = new Variable( mHeight++, true, _ex );
        mRows.push_back( TableauHead() );
        EntryID currentStartEntryOfRow = 0;
        vector< Variable* >::const_iterator basicVar = _nonbasicVariables.begin();
        vector< numeric >::iterator coeff = _coefficients.begin();
        while( basicVar != _nonbasicVariables.end() )
        {
            EntryID entry = newTableauEntry();
            // Fix the position.
            (*mpEntries)[entry].setColumnNumber( (*basicVar)->position() );
            (*mpEntries)[entry].setRowNumber( mHeight-1 );
            // Set the content.
            (*mpEntries)[entry].rContent() = *coeff;
            // Set it as column end.
            if( mColumns[(*mpEntries)[entry].columnNumber()].mStartEntry != 0 )
            {
                (*mpEntries)[mColumns[(*mpEntries)[entry].columnNumber()].mStartEntry].setDown( entry );
            }
            (*mpEntries)[entry].setUp( mColumns[(*mpEntries)[entry].columnNumber()].mStartEntry );
            mColumns[(*mpEntries)[entry].columnNumber()].mStartEntry = entry;
            ++mColumns[(*mpEntries)[entry].columnNumber()].mSize;
            (*mpEntries)[entry].setDown( 0 );
            // Put it in the row.
            if( currentStartEntryOfRow == 0 )
            {
                currentStartEntryOfRow = entry;
            }
            else
            {
                Iterator rowIter = Iterator( currentStartEntryOfRow, mpEntries );
                while( !rowIter.rowEnd() && (*rowIter).columnNumber() < (*mpEntries)[entry].columnNumber() )
                {
                    rowIter.right();
                }
                assert( (*rowIter).columnNumber() !=  (*mpEntries)[entry].columnNumber() );
                if( (*rowIter).columnNumber() > (*mpEntries)[entry].columnNumber() )
                {
                    // Entry horizontally between two entries.
                    EntryID leftEntryID = (*rowIter).left();
                    if( leftEntryID != 0 )
                    {
                        (*mpEntries)[leftEntryID].setRight( entry );
                    }
                    (*rowIter).setLeft( entry );
                    (*mpEntries)[entry].setLeft( leftEntryID );
                    (*mpEntries)[entry].setRight( rowIter.entryID() );
                    if( leftEntryID == 0 )
                    {
                        currentStartEntryOfRow = entry;
                    }
                }
                else
                {
                    // Entry will be the rightmost in this row.
                    (*rowIter).setRight( entry );
                    (*mpEntries)[entry].setLeft( rowIter.entryID() );
                    (*mpEntries)[entry].setRight( 0 );
                }
            }
            ++basicVar;
            ++coeff;
        }
        mRows[mHeight-1].mStartEntry = currentStartEntryOfRow;
        mRows[mHeight-1].mSize = _nonbasicVariables.size();
        mRows[mHeight-1].mName = var;
        return var;
    }

    #ifdef LRA_USE_PIVOTING_STRATEGY
    /**
     *
     * @param y
     * @param x
     * @return
     */
    static unsigned luby( unsigned _numberOfRestarts )
    {
        // Find the finite subsequence that contains index 'x', and the
        // size of that subsequence:
        cout << "_numberOfRestarts = " << _numberOfRestarts;
        unsigned size, seq;
        for( size = 1, seq = 0; size < _numberOfRestarts + 1; seq++, size = 2 * size + 1 );

        while( size - 1 != _numberOfRestarts )
        {
            size = (size - 1) >> 1;
            seq--;
            _numberOfRestarts = _numberOfRestarts % size;
        }
        cout << " results in seq = " << seq << endl;
        if( seq >= 64 ) return 0;
        cout << " results in seq = " << seq << endl;
        unsigned result = 1;
        result = result << seq;
        cout << "result = " << result << endl;
        return result;
    }
    #endif

    /**
     *
     * @return
     */
    pair<EntryID,bool> Tableau::nextPivotingElement()
    {
        #ifdef LRA_USE_PIVOTING_STRATEGY
        //  Dynamic strategy for a fixed number of steps
        if( mPivotingSteps >= mNextRestartBegin && mPivotingSteps < mNextRestartEnd )
        {
            unsigned smallestRowSize = mWidth;
            unsigned smallestColumnSize = mHeight;
            EntryID beginOfBestRow = 0;
            EntryID beginOfFirstConflictRow = 0;
            for( unsigned rowNumber = 0; rowNumber < mRows.size(); ++rowNumber )
            {
                Value theta = Value();
                pair<EntryID,bool> result = isSuitable( rowNumber, theta );
                if( !result.second )
                {
                    // Found a conflicting row.
                    if( beginOfFirstConflictRow == 0 )
                    {
                        beginOfFirstConflictRow = result.first;
                    }
                }
                else if( result.first != 0 )
                {
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
            for( unsigned rowNumber = 0; rowNumber < mRows.size(); ++rowNumber )
            {
                pair<EntryID,bool> result = isSuitable( rowNumber, *mpTheta );
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
        // Upper bound is violated
        if( mRows[_rowNumber].mName->supremum() < mRows[_rowNumber].mName->assignment() )
        {
            // Check all entries in the row / basic variables
            Iterator rowIter = Iterator( mRows[_rowNumber].mStartEntry, mpEntries );
            while( true )
            {
                if( (*rowIter).content().info( info_flags::negative ) )
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment() )
                    {
                        // Basic variable suitable
                        assert( (*rowIter).content() != 0 );
                        _theta = (mRows[_rowNumber].mName->supremum().limit() - mRows[_rowNumber].mName->assignment())/(*rowIter).content();
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                else
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment()  )
                    {
                        // Basic variable suitable
                        assert( (*rowIter).content() != 0 );
                        _theta = (mRows[_rowNumber].mName->supremum().limit() - mRows[_rowNumber].mName->assignment())/(*rowIter).content();
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                // No suitable basic variable -> UNSAT
                if( rowIter.rowEnd() )
                {
                    return pair<EntryID,bool>( 0, false );
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        // Lower bound is violated
        else if( mRows[_rowNumber].mName->infimum() > mRows[_rowNumber].mName->assignment() )
        {
            // Check all entries in the row / basic variables
            Iterator rowIter = Iterator( mRows[_rowNumber].mStartEntry, mpEntries );
            while( true )
            {
                if( (*rowIter).content().info( info_flags::positive ) )
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->supremum() > mColumns[(*rowIter).columnNumber()].mName->assignment() )
                    {
                        // Basic variable suitable
                        assert( (*rowIter).content() != 0 );
                        _theta = (mRows[_rowNumber].mName->infimum().limit() - mRows[_rowNumber].mName->assignment())/(*rowIter).content();
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                else
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment() )
                    {
                        // Basic variable suitable
                        assert( (*rowIter).content() != 0 );
                        _theta = (mRows[_rowNumber].mName->infimum().limit() - mRows[_rowNumber].mName->assignment())/(*rowIter).content();
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                // No suitable basic variable -> UNSAT
                if( rowIter.rowEnd() )
                {
                    return pair<EntryID,bool>( 0, false );
                }
                else
                {
                    rowIter.right();
                }
            }
        }
        // No bound is violated
        return pair<EntryID,bool>( 0, true );
    }

    /**
     *
     * @param _startRow
     * @return
     */
    vector< set< const Bound* > > Tableau::getConflicts( EntryID _rowEntry ) const
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
                basic.rAssignment() = basic.assignment() + (_change * (*columnIter).content());
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
        Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowBegin() )
        {
            iterTemp.left();
            (*iterTemp).rContent() = -(*iterTemp).content()/(*mpEntries)[_pivotingElement].content();
            pivotingRowLeftSide.push_back( iterTemp );
        }
        // Then the column with ** right to the pivoting column until the rightmost column with **.
        vector<Iterator> pivotingRowRightSide = vector<Iterator>();
        iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowEnd() )
        {
            iterTemp.right();
            (*iterTemp).rContent() = -(*iterTemp).content()/(*mpEntries)[_pivotingElement].content();
            pivotingRowRightSide.push_back( iterTemp );
        }
        // Update the assignments of the pivoting variables
        Variable* nameTmp = mRows[(*mpEntries)[_pivotingElement].rowNumber()].mName;
        nameTmp->rAssignment() = nameTmp->assignment() + (*mpTheta) * (*mpEntries)[_pivotingElement].content();
        mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName->rAssignment() = mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName->assignment() + (*mpTheta);
        // Update the content of the pivoting entry
        (*mpEntries)[_pivotingElement].rContent() = 1/(*mpEntries)[_pivotingElement].content();
        // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
        // For all rows R having a nonzero entry in the pivoting column:
        //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
        //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
        if( (*mpEntries)[_pivotingElement].up() == 0 )
        {
            updateDownwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        else if( (*mpEntries)[_pivotingElement].down() == 0 )
        {
            updateUpwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        else
        {
            updateDownwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
            updateUpwards( _pivotingElement, pivotingRowLeftSide, pivotingRowRightSide );
        }
        // Swap the row and the column head.
        unsigned activityTmp = mRows[(*mpEntries)[_pivotingElement].rowNumber()].mActivity;
        mRows[(*mpEntries)[_pivotingElement].rowNumber()].mName = mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName;
        mRows[(*mpEntries)[_pivotingElement].rowNumber()].mActivity = mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mActivity;
        mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName = nameTmp;
        mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mActivity = activityTmp;
        // Adapt both variables.
        Variable& basicVar = *mRows[(*mpEntries)[_pivotingElement].rowNumber()].mName;
        basicVar.rPosition() = (*mpEntries)[_pivotingElement].rowNumber();
        basicVar.setBasic( true );
        Variable& nonbasicVar = *mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName;
        nonbasicVar.rPosition() = (*mpEntries)[_pivotingElement].columnNumber();
        nonbasicVar.setBasic( false );
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
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() = mRows[(*pivotingColumnIter).rowNumber()].mName->assignment()
                                                                            + (*mpTheta) * (*pivotingColumnIter).content();
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
                // TODO: refine the current row
                while( !currentRowIter.rowBegin() && (*currentRowIter).columnNumber() > (**currentColumnIter).columnNumber() )
                {
                    currentRowIter.left();
                }
                // Update the entry
                if( (*currentColumnIter) == currentRowIter )
                {
                    // Entry already exists, so update it only and maybe remove it.
                    (*currentRowIter).rContent() = (*currentRowIter).content() + (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    if( (*currentRowIter).content() == 0 )
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
                    // Set the position.
                    (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID upperEntryID = (**currentColumnIter).up();
                        if( upperEntryID != 0 )
                        {
                            (*mpEntries)[upperEntryID].setDown( entryID );
                        }
                        (**currentColumnIter).setUp( entryID );
                        (*mpEntries)[entryID].setUp( upperEntryID );
                        (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the lowest in this column.
                        (**currentColumnIter).setDown( entryID );
                        (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                        (*mpEntries)[entryID].setDown( 0 );
                        mColumns[(*mpEntries)[entryID].columnNumber()].mStartEntry = entryID;
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
                        (*mpEntries)[entryID].setRight( rightEntryID );
                        (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the leftmost in this row.
                        (*currentRowIter).setLeft( entryID );
                        (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                        (*mpEntries)[entryID].setLeft( 0 );
                        mRows[(*mpEntries)[entryID].rowNumber()].mStartEntry = entryID;
                    }
                    // Set the content of the entry.
                    ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                    ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                    (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
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
                    (*currentRowIter).rContent() = (*currentRowIter).content() + (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    if( (*currentRowIter).content() == 0 )
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
                    // Set the position.
                    (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID upperEntryID = (**currentColumnIter).up();
                        if( upperEntryID != 0 )
                        {
                            (*mpEntries)[upperEntryID].setDown( entryID );
                        }
                        (**currentColumnIter).setUp( entryID );
                        (*mpEntries)[entryID].setUp( upperEntryID );
                        (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the lowest in this column.
                        (**currentColumnIter).setDown( entryID );
                        (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                        (*mpEntries)[entryID].setDown( 0 );
                        mColumns[(*mpEntries)[entryID].columnNumber()].mStartEntry = entryID;
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
                        (*mpEntries)[entryID].setLeft( leftEntryID );
                        (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the rightmost in this row.
                        (*currentRowIter).setRight( entryID );
                        (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                        (*mpEntries)[entryID].setRight( 0 );
                    }
                    // Set the content of the entry.
                    ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                    ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                    (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() = (*pivotingColumnIter).content() * (*mpEntries)[_pivotingElement].content();
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
            mRows[(*pivotingColumnIter).rowNumber()].mName->rAssignment() = mRows[(*pivotingColumnIter).rowNumber()].mName->assignment()
                                                                            + (*mpTheta) * (*pivotingColumnIter).content();
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
                    (*currentRowIter).rContent() = (*currentRowIter).content() + (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    if( (*currentRowIter).content() == 0 )
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
                    // Set the position.
                    (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID lowerEntryID = (**currentColumnIter).down();
                        if( lowerEntryID != 0 )
                        {
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                        }
                        (**currentColumnIter).setDown( entryID );
                        (*mpEntries)[entryID].setDown( lowerEntryID );
                        (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        (**currentColumnIter).setUp( entryID );
                        (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                        (*mpEntries)[entryID].setUp( 0 );
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
                        (*mpEntries)[entryID].setRight( rightEntryID );
                        (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                    }
                    else
                    {
                        (*currentRowIter).setLeft( entryID );
                        (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                        (*mpEntries)[entryID].setLeft( 0 );
                        mRows[(*mpEntries)[entryID].rowNumber()].mStartEntry = entryID;
                    }
                    // Set the content of the entry.
                    ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                    ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                    (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
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
                    (*currentRowIter).rContent() = (*currentRowIter).content() + (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    if( (*currentRowIter).content() == 0 )
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
                    // Set the position.
                    (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                    (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                    if( (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                    {
                        // Entry vertically between two entries.
                        EntryID lowerEntryID = (**currentColumnIter).down();
                        if( lowerEntryID != 0 )
                        {
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                        }
                        (**currentColumnIter).setDown( entryID );
                        (*mpEntries)[entryID].setDown( lowerEntryID );
                        (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                    }
                    else
                    {
                        // Entry will be the uppermost in this column.
                        (**currentColumnIter).setUp( entryID );
                        (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                        (*mpEntries)[entryID].setUp( 0 );
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
                        (*mpEntries)[entryID].setLeft( leftEntryID );
                        (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                    }
                    else
                    {
                        // Entry will be the rightmost in this row.
                        (*currentRowIter).setRight( entryID );
                        (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                        (*mpEntries)[entryID].setRight( 0 );
                    }
                    // Set the content of the entry.
                    ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                    ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                    (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() = (*pivotingColumnIter).content() * (*mpEntries)[_pivotingElement].content();
        }
    }

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