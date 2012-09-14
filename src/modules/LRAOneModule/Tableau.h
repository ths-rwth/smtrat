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
 * @author name surname <emailadress>
 *
 * @version 2012-04-05
 * Created on April 5th, 2012, 3:22 PM
 */

#ifndef TABLEAU_H
#define TABLEAU_H

#include <vector>
#include <stack>
#include <map>
#include "Variable.h"

#define LRA_USE_PIVOTING_STRATEGY
#define LRA_REFINEMENT
//#define LRA_PROPAGATE_NEW_CONSTRAINTS

namespace lraone
{
    typedef unsigned EntryID;

    class TableauEntry
    {
        private:
            EntryID         mUp;
            EntryID         mDown;
            EntryID         mLeft;
            EntryID         mRight;
            unsigned        mRowNumber;
            unsigned        mColumnNumber;
            GiNaC::numeric* mpContent;

        public:
            TableauEntry():
                mUp( 0 ),
                mDown( 0 ),
                mLeft( 0 ),
                mRight( 0 ),
                mRowNumber( 0 ),
                mColumnNumber( 0 ),
                mpContent( NULL )
            {}
            ;
            TableauEntry( EntryID _up,
                          EntryID _down,
                          EntryID _left,
                          EntryID _right,
                          unsigned _rowNumber,
                          unsigned _columnNumber,
                          GiNaC::numeric* _content ):
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

            const GiNaC::numeric& content() const
            {
                return *mpContent;
            }

            GiNaC::numeric& rContent()
            {
                return *mpContent;
            }

            GiNaC::numeric* const pContent() const
            {
                return mpContent;
            }
    };

    class Tableau
    {
        private:
            struct TableauHead
            {
                EntryID   mStartEntry;
                unsigned  mSize;
                Variable* mName;
                unsigned  mActivity;
            };
            unsigned                   mHeight;
            unsigned                   mWidth;
            unsigned                   mPivotingSteps;
            #ifdef LRA_USE_PIVOTING_STRATEGY
            unsigned                   mRestarts;
            unsigned                   mNextRestartBegin;
            unsigned                   mNextRestartEnd;
            #endif
            std::stack<EntryID>        mUnusedIDs;
            std::vector<TableauHead>   mRows;    // First element is the head of the row and the second the length of the row.
            std::vector<TableauHead>   mColumns;    // First element is the end of the column and the second the length of the column.
            std::vector<TableauEntry>* mpEntries;
            Value*                     mpTheta;
            #ifdef LRA_REFINEMENT
            std::vector<std::pair<const Bound*, std::vector<smtrat::Formula*> > >  mLearnedBounds;
            #endif

            class Iterator
            {
                private:
                    unsigned                   mEntryID;
                    std::vector<TableauEntry>* mpEntries;

                public:
                    Iterator( EntryID _start, std::vector<TableauEntry>* const _entries ):
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

                    TableauEntry& operator *()
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

                    std::vector<TableauEntry>* const pEntries() const
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
            };    /* class Tableau::Iterator */

        public:
            Tableau();
            ~Tableau();

            void setSize( unsigned _expectedHeight, unsigned _expectedWidth )
            {
                mRows.reserve( _expectedHeight );
                mColumns.reserve( _expectedWidth );
                mpEntries->reserve( _expectedHeight*_expectedWidth+1 );
            }

            #ifdef LRA_USE_PIVOTING_STRATEGY
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

            void incrementBasicActivity( const Variable& _var )
            {
                ++mRows[_var.position()].mActivity;
            }

            void incrementNonbasicActivity( const Variable& _var )
            {
                ++mColumns[_var.position()].mActivity;
            }

            void decrementBasicActivity( const Variable& _var )
            {
                assert( mRows[_var.position()].mActivity != 0 );
                --mRows[_var.position()].mActivity;
            }

            void decrementNonbasicActivity( const Variable& _var )
            {
                assert( mColumns[_var.position()].mActivity != 0 );
                --mColumns[_var.position()].mActivity;
            }

            unsigned numberOfPivotingSteps() const
            {
                return mPivotingSteps;
            }

            #ifdef LRA_REFINEMENT
            std::vector<std::pair<const Bound*, std::vector<smtrat::Formula*> > >& learnedBounds()
            {
                return mLearnedBounds;
            }
            #endif

            EntryID newTableauEntry();
            void removeEntry( EntryID );
            Variable* newNonbasicVariable( const GiNaC::ex* );
            Variable* newBasicVariable( const GiNaC::ex*, const std::vector<Variable*>&, std::vector<GiNaC::numeric>& );
            std::pair<EntryID, bool> nextPivotingElement();
            std::pair<EntryID, bool> isSuitable( EntryID, Value& ) const;
            bool betterEntry( EntryID, EntryID ) const;
            std::vector< const Bound* > getConflict( EntryID ) const;
            std::vector< std::set< const Bound* > > getConflictsFrom( EntryID ) const;
            void updateBasicAssignments( unsigned, const Value& );
            void pivot( EntryID );
            void updateDownwards( EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
            void updateUpwards( EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
            #ifdef LRA_REFINEMENT
            void upperRefinement( const TableauHead& );
            void lowerRefinement( const TableauHead& );
            #endif
            unsigned checkCorrectness() const;
            bool rowCorrect( unsigned _rowNumber ) const;
            void printHeap( std::ostream& = std::cout, unsigned = 30, const std::string = "" ) const;
            void printEntry( std::ostream& = std::cout, EntryID = 0, unsigned = 20 ) const;
            void printVariables( std::ostream& = std::cout, const std::string = "" ) const;
            void print( std::ostream& = std::cout, unsigned = 28, const std::string = "" ) const;

    };
}    // end namspace lra

#endif   /* TABLEAU_H */
