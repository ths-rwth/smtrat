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
        mUnusedIDs(),
        mRows(),
        mColumns()
    {
        mpEntries = new vector< TableauEntry >();
        mpEntries->push_back( TableauEntry() );
    };

    Tableau::~Tableau()
    {
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
        else
        {
            mColumns[(*mpEntries)[_entryID].columnNumber()].mStartEntry = (*mpEntries)[_entryID].down();
        }
        if( (*mpEntries)[_entryID].down() != 0 )
        {
            (*mpEntries)[(*mpEntries)[_entryID].down()].setUp( (*mpEntries)[_entryID].up() );
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
        vector< Variable* >::const_iterator basicVar = _nonbasicVariables.begin();
        vector< numeric >::iterator coeff = _coefficients.begin();
        EntryID lastRowEntry = 0;
        while( basicVar != _nonbasicVariables.end() )
        {
            EntryID entry = newTableauEntry();
            if( lastRowEntry == 0 ) mRows[mHeight-1].mStartEntry = entry;
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
            if( lastRowEntry != 0 )
            {
                (*mpEntries)[lastRowEntry].setRight( entry );
            }
            (*mpEntries)[entry].setLeft( lastRowEntry );
            ++basicVar;
            ++coeff;
            if( basicVar == _nonbasicVariables.end() )
            {
                (*mpEntries)[entry].setRight( 0 );
            }
            else
            {
                lastRowEntry = entry;
            }
        }
        mRows[mHeight-1].mSize = _nonbasicVariables.size();
        mRows[mHeight-1].mName = var;
        return var;
    }

    /**
     *
     * @return
     */
    pair<EntryID,bool> Tableau::nextPivotingElement() const
    {
        // Dynamic strategy for a fixed number of steps
        if( false ) //mPivotingSteps > mWidth )
        {
            unsigned smallestRowSize = mWidth;
            unsigned smallestColumnSize = mHeight;
            EntryID beginOfBestRow = 0;
            for( unsigned rowNumber = 0; rowNumber < mRows.size(); ++rowNumber )
            {
                pair<EntryID,bool> result = isSuitable( rowNumber );
                if( result.first != 0 && result.second )
                {
                    if( mRows[(*mpEntries)[result.first].rowNumber()].mSize < smallestRowSize )
                    {
                        // Found a better pivoting element.
                        smallestRowSize = mRows[(*mpEntries)[result.first].rowNumber()].mSize;
                        smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                        beginOfBestRow = result.first;
                    }
                    else if( mRows[(*mpEntries)[result.first].rowNumber()].mSize == smallestRowSize
                             && mColumns[(*mpEntries)[result.first].columnNumber()].mSize < smallestColumnSize )
                    {
                        // Found a better pivoting element.
                        smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                        beginOfBestRow = result.first;
                    }
                }
                else if( !result.second )
                {
                    // Found a conflicting row.
                    return pair<EntryID,bool>( result.first, false );
                }
            }
            if( beginOfBestRow != 0 )
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
            for( unsigned rowNumber = 0; rowNumber < mRows.size(); ++rowNumber )
            {
                pair<EntryID,bool> result = isSuitable( rowNumber );
                if( result.first != 0 )
                {
                    if( result.second )
                    {
                        // Found a pivoting element
                        return pair<EntryID,bool>( result.first, true );
                    }
                    else
                    {
                        // Found a conflicting row.
                        return pair<EntryID,bool>( result.first, false );
                    }
                }
            }
            // Found no pivoting element, that is no variable violates its bounds.
            return pair<EntryID,bool>( 0, true );
        }
    }

    /**
     *
     * @param _rowNumber
     * @return
     */
    pair<EntryID,bool> Tableau::isSuitable( unsigned _rowNumber ) const
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
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                else
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment()  )
                    {
                        // Basic variable suitable
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
                        return pair<EntryID,bool>( rowIter.entryID(), true );
                    }
                }
                else
                {
                    if( mColumns[(*rowIter).columnNumber()].mName->infimum() < mColumns[(*rowIter).columnNumber()].mName->assignment() )
                    {
                        // Basic variable suitable
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

    void Tableau::updateBasicAssignments( unsigned _column, const Value& _change )
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

    /**
     *
     * @param _pivotingElement
     */
    void Tableau::pivot( EntryID _pivotingElement )
    {
        // Find all columns having "a nonzero entry in the pivoting row"**, update this entry and store it.
        // First the column with ** left to the pivoting column until the leftmost column with **.
        vector<Iterator> pivotingRow = vector<Iterator>();
        Iterator iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowBegin() )
        {
            iterTemp.left();
            (*iterTemp).rContent() = -(*iterTemp).content()/(*mpEntries)[_pivotingElement].content();
            pivotingRow.push_back( iterTemp );
        }
        // Then the column with ** right to the pivoting column until the rightmost column with **.
        iterTemp = Iterator( _pivotingElement, mpEntries );
        while( !iterTemp.rowEnd() )
        {
            iterTemp.right();
            (*iterTemp).rContent() = -(*iterTemp).content()/(*mpEntries)[_pivotingElement].content();
            pivotingRow.push_back( iterTemp );
        }
        (*mpEntries)[_pivotingElement].rContent() = 1/(*mpEntries)[_pivotingElement].content();

        // Let (p_r,p_c,p_e) be the pivoting entry, where p_r is the row number, p_c the column number and p_e the content.
        // For all rows R having a nonzero entry in the pivoting column:
        //    For all columns C having a nonzero entry (r_r,r_c,r_e) in the pivoting row:
        //        Update the entry (t_r,t_c,t_e) of the intersection of R and C to (t_r,t_c,t_e+r_e).
        if( (*mpEntries)[_pivotingElement].up() == 0 )
        {
            updateDownwards( _pivotingElement, pivotingRow );
        }
        else if( (*mpEntries)[_pivotingElement].down() == 0 )
        {
            updateUpwards( _pivotingElement, pivotingRow );
        }
        else
        {
            updateDownwards( _pivotingElement, pivotingRow );
            updateUpwards( _pivotingElement, pivotingRow );
        }
        // Swap the row and the column head.
        Variable* nameTmp = mRows[(*mpEntries)[_pivotingElement].rowNumber()].mName;
        mRows[(*mpEntries)[_pivotingElement].rowNumber()].mName = mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName;
        mColumns[(*mpEntries)[_pivotingElement].columnNumber()].mName = nameTmp;
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
    void Tableau::updateDownwards( EntryID _pivotingElement, vector<Iterator>& _pivotingRow )
    {
        vector<Iterator> columnIters = vector<Iterator>( _pivotingRow );
        Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
        do
        {
            pivotingColumnIter.down();
            Iterator currentRowIter = pivotingColumnIter;
            bool directionChanged = false;
            auto pivotingRowIter = _pivotingRow.begin();
            for( auto currentColumnIter = columnIters.begin(); currentColumnIter != columnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRow.end() );
                while( !(*currentColumnIter).columnEnd() && (**currentColumnIter).rowNumber() < (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).down();
                }
                if( directionChanged )
                {
                    while( !currentRowIter.rowBegin() && (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
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
                            removeEntry( currentRowIter.entryID() );
                        }
                    }
                    else
                    {
                        EntryID entryID = newTableauEntry();
                        // Set the position.
                        (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                        (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                        if( (*currentColumnIter).columnEnd() )
                        {
                            // Entry will be the lowest in this column.
                            (**currentColumnIter).setDown( entryID );
                            (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                            (*mpEntries)[entryID].setDown( 0 );
                        }
                        else
                        {
                            // Entry vertically between to entries.
                            EntryID upperEntryID = (**currentColumnIter).up();
                            (*mpEntries)[upperEntryID].setDown( entryID );
                            (**currentColumnIter).setUp( entryID );
                            (*mpEntries)[entryID].setUp( upperEntryID );
                            (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                        }
                        if( currentRowIter.rowBegin() )
                        {
                            // Entry will be the rightmost in this row.
                            (*currentRowIter).setRight( entryID );
                            (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                            (*mpEntries)[entryID].setRight( 0 );
                        }
                        else
                        {
                            // Entry horizontally between to entries.
                            EntryID leftEntryID = (*currentRowIter).left();
                            (*mpEntries)[leftEntryID].setRight( entryID );
                            (*currentRowIter).setLeft( entryID );
                            (*mpEntries)[entryID].setLeft( leftEntryID );
                            (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                        }
                        // Set the content of the entry.
                        ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                        ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                        (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    }
                }
                else
                {
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
                            removeEntry( currentRowIter.entryID() );
                        }
                    }
                    else
                    {
                        EntryID entryID = newTableauEntry();
                        // Set the position.
                        (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                        (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                        if( (*currentColumnIter).columnEnd() )
                        {
                            // Entry will be the lowest in this column.
                            (**currentColumnIter).setDown( entryID );
                            (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                            (*mpEntries)[entryID].setDown( 0 );
                        }
                        else
                        {
                            // Entry vertically between to entries.
                            EntryID upperEntryID = (**currentColumnIter).up();
                            (*mpEntries)[upperEntryID].setDown( entryID );
                            (**currentColumnIter).setUp( entryID );
                            (*mpEntries)[entryID].setUp( upperEntryID );
                            (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                        }
                        if( currentRowIter.rowBegin() )
                        {
                            // Entry will be the leftmost in this row.
                            (*currentRowIter).setLeft( entryID );
                            (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                            (*mpEntries)[entryID].setLeft( 0 );
                            mRows[(*mpEntries)[entryID].rowNumber()].mStartEntry = entryID;
                        }
                        else
                        {
                            // Entry horizontally between to entries.
                            EntryID rightEntryID = (*currentRowIter).right();
                            (*mpEntries)[rightEntryID].setLeft( entryID );
                            (*currentRowIter).setRight( entryID );
                            (*mpEntries)[entryID].setRight( rightEntryID );
                            (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                        }
                        // Set the content of the entry.
                        ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                        ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                        (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    }
                }
                if( (*currentColumnIter).rowBegin() )
                {
                    currentRowIter = pivotingColumnIter;
                    directionChanged = true;
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() = (*pivotingColumnIter).content() * (*mpEntries)[_pivotingElement].content();
        }
        while( !pivotingColumnIter.columnEnd() );
    }

    /**
     *
     * @param _pivotingElement
     * @param _pivotingRow
     */
    void Tableau::updateUpwards( EntryID _pivotingElement, vector<Iterator>& _pivotingRow )
    {
        vector<Iterator> columnIters = vector<Iterator>( _pivotingRow );
        Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
        do
        {
            pivotingColumnIter.up();
            Iterator currentRowIter = pivotingColumnIter;
            bool directionChanged = false;
            auto pivotingRowIter = _pivotingRow.begin();
            for( auto currentColumnIter = columnIters.begin(); currentColumnIter != columnIters.end(); ++currentColumnIter )
            {
                assert( pivotingRowIter != _pivotingRow.end() );
                while( !(*currentColumnIter).columnBegin() && (**currentColumnIter).rowNumber() > (*pivotingColumnIter).rowNumber() )
                {
                    (*currentColumnIter).up();
                }
                if( directionChanged )
                {
                    while( !currentRowIter.rowBegin() && (*currentRowIter).columnNumber() < (**currentColumnIter).columnNumber() )
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
                            removeEntry( currentRowIter.entryID() );
                        }
                    }
                    else
                    {
                        EntryID entryID = newTableauEntry();
                        // Set the position.
                        (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                        (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                        if( (*currentColumnIter).columnBegin() )
                        {
                            // Entry will be the uppermost in this column.
                            (**currentColumnIter).setUp( entryID );
                            (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                            (*mpEntries)[entryID].setUp( 0 );
                            mColumns[(*mpEntries)[entryID].columnNumber()].mStartEntry = entryID;
                        }
                        else
                        {
                            // Entry vertically between to entries.
                            EntryID lowerEntryID = (**currentColumnIter).down();
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                            (**currentColumnIter).setDown( entryID );
                            (*mpEntries)[entryID].setDown( lowerEntryID );
                            (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                        }
                        if( currentRowIter.rowBegin() )
                        {
                            // Entry will be the rightmost in this row.
                            (*currentRowIter).setRight( entryID );
                            (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                            (*mpEntries)[entryID].setRight( 0 );
                        }
                        else
                        {
                            // Entry horizontally between to entries.
                            EntryID leftEntryID = (*currentRowIter).left();
                            (*mpEntries)[leftEntryID].setRight( entryID );
                            (*currentRowIter).setLeft( entryID );
                            (*mpEntries)[entryID].setLeft( leftEntryID );
                            (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                        }
                        // Set the content of the entry.
                        ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                        ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                        (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    }
                }
                else
                {
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
                            removeEntry( currentRowIter.entryID() );
                        }
                    }
                    else
                    {
                        EntryID entryID = newTableauEntry();
                        // Set the position.
                        (*mpEntries)[entryID].setRowNumber( (*mpEntries)[currentRowIter.entryID()].rowNumber() );
                        (*mpEntries)[entryID].setColumnNumber( (*mpEntries)[(*currentColumnIter).entryID()].columnNumber() );
                        if( (*currentColumnIter).columnBegin() )
                        {
                            // Entry will be the uppermost in this column.
                            (**currentColumnIter).setUp( entryID );
                            (*mpEntries)[entryID].setDown( (*currentColumnIter).entryID() );
                            (*mpEntries)[entryID].setUp( 0 );
                            mColumns[(*mpEntries)[entryID].columnNumber()].mStartEntry = entryID;
                        }
                        else
                        {
                            // Entry vertically between to entries.
                            EntryID lowerEntryID = (**currentColumnIter).down();
                            (*mpEntries)[lowerEntryID].setUp( entryID );
                            (**currentColumnIter).setDown( entryID );
                            (*mpEntries)[entryID].setDown( lowerEntryID );
                            (*mpEntries)[entryID].setUp( (*currentColumnIter).entryID() );
                        }
                        if( currentRowIter.rowBegin() )
                        {
                            // Entry will be the leftmost in this row.
                            (*currentRowIter).setLeft( entryID );
                            (*mpEntries)[entryID].setRight( currentRowIter.entryID() );
                            (*mpEntries)[entryID].setLeft( 0 );
                            mRows[(*mpEntries)[entryID].rowNumber()].mStartEntry = entryID;
                        }
                        else
                        {
                            // Entry horizontally between to entries.
                            EntryID rightEntryID = (*currentRowIter).right();
                            (*mpEntries)[rightEntryID].setLeft( entryID );
                            (*currentRowIter).setRight( entryID );
                            (*mpEntries)[entryID].setRight( rightEntryID );
                            (*mpEntries)[entryID].setLeft( currentRowIter.entryID() );
                        }
                        // Set the content of the entry.
                        ++mRows[(*mpEntries)[entryID].rowNumber()].mSize;
                        ++mColumns[(*mpEntries)[entryID].columnNumber()].mSize;
                        (*mpEntries)[entryID].rContent() = (*pivotingColumnIter).content()*(**pivotingRowIter).content();
                    }
                }
                if( (*currentColumnIter).rowBegin() )
                {
                    currentRowIter = pivotingColumnIter;
                    directionChanged = true;
                }
                ++pivotingRowIter;
            }
            (*pivotingColumnIter).rContent() = (*pivotingColumnIter).content() * (*mpEntries)[_pivotingElement].content();
        }
        while( !pivotingColumnIter.columnEnd() );
    }

    void Tableau::printHeap( ostream& _out, unsigned _maxEntryLength ) const
    {
        for( EntryID pos = 0; pos < mpEntries->size(); ++pos )
        {
            printEntry( _out, pos, _maxEntryLength );
            _out << endl;
        }
    }

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

    void Tableau::printVariables( ostream& _out ) const
    {
        _out << "Basic variables:" << endl;
        for( vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
            _out << "  ";
            row->mName->print( _out );
            _out << endl << "    starts with the entry ( ";
            printEntry( _out, row->mStartEntry );
            _out << ") with " << row->mSize << " entries" << endl;
        }
        _out << "Nonbasic variables:" << endl;
        for( vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            _out << "  ";
            column->mName->print( _out );
            _out << endl << "    starts with the entry ( ";
            printEntry( _out, column->mStartEntry );
            _out << ") with " << column->mSize << " entries" << endl;
        }
    }

    void Tableau::print( ostream& _out, unsigned _maxEntryLength ) const
    {
        char     frameSign     = '-';
        _out << setw( _maxEntryLength * (mWidth + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setw( _maxEntryLength ) << setfill( ' ' ) << "#";
        for( vector<TableauHead>::const_iterator column = mColumns.begin(); column != mColumns.end(); ++column )
        {
            stringstream out;
            out << *column->mName->pExpression();
            _out << setw( _maxEntryLength ) << out.str() + " #";
        }
        _out << endl;
        _out << setw( _maxEntryLength * (mWidth + 1) ) << setfill( '#' ) << "" << endl;
        _out << setfill( ' ' );
        for( vector<TableauHead>::const_iterator row = mRows.begin(); row != mRows.end(); ++row )
        {
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
                if( rowIter.rowEnd() )
                {
                    for( unsigned i = currentColumn+1; i < mWidth; ++i )
                    {
                        _out << setw( _maxEntryLength ) << "0 #";
                    }
                    _out << endl;
                    break;
                }
                rowIter.right();
                currentColumn = (*rowIter).columnNumber();
            }
        }
        _out << setw( _maxEntryLength * (mWidth + 1) ) << setfill( frameSign ) << "" << endl;
        _out << setfill( ' ' );
    }

}  // end namspace lra