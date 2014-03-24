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

#define LRA_USE_PIVOTING_STRATEGY
#define LRA_REFINEMENT
#define LRA_LOCAL_CONFLICT_DIRECTED
//#define LRA_PRINT_STATS
//#define LRA_USE_OCCURENCE_STRATEGY
#ifndef LRA_USE_OCCURENCE_STRATEGY
#define LRA_USE_THETA_STRATEGY
#endif
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
                    const Bound<T1, T2>*                newBound;
                    const Bound<T1, T2>*                nextWeakerBound;
                    std::vector< const Bound<T1, T2>*>* premise;
                };
            private:
                bool                            mRowsCompressed;
                size_t                          mWidth;
                size_t                          mPivotingSteps;
                #ifdef LRA_USE_PIVOTING_STRATEGY
                size_t                          mMaxPivotsWithoutBlandsRule;
                #endif
                smtrat::Formula::iterator       mDefaultBoundPosition;
                std::stack<EntryID>             mUnusedIDs;
                std::vector<Variable<T1,T2>*>   mRows;       // First element is the head of the row and the second the length of the row.
                std::vector<Variable<T1,T2>*>   mColumns;    // First element is the end of the column and the second the length of the column.
                std::list<std::list<std::pair<Variable<T1,T2>*,T2>>> mNonActiveBasics;
                std::vector<TableauEntry<T1,T2> >* mpEntries;
                std::vector<Variable<T1,T2>*>   mConflictingRows;
                Value<T1>*                      mpTheta;
                #ifdef LRA_REFINEMENT
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedLowerBounds;
                std::map<Variable<T1,T2>*, LearnedBound> mLearnedUpperBounds;
                std::vector<typename std::map<Variable<T1,T2>*, LearnedBound>::iterator> mNewLearnedBounds;
                #endif

                class Iterator
                {
                    private:
                        EntryID                   mEntryID;
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
                Tableau( smtrat::Formula::iterator );
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
                Variable<T1, T2>* newNonbasicVariable( const smtrat::Polynomial* );
                Variable<T1, T2>* newBasicVariable( const smtrat::Polynomial*, std::map<carl::Variable, Variable<T1, T2>*>& );
                void activateBasicVar( Variable<T1, T2>* );
                void deactivateBasicVar( Variable<T1, T2>* );
                void compressRows();
                void activateBound( const Bound<T1, T2>* );
                void deactivateBound( const Bound<T1, T2>* );
                std::pair<EntryID, bool> nextPivotingElement();
                std::pair<EntryID, bool> isSuitable( const Variable<T1, T2>&, Value<T1>& ) const;
                bool betterEntry( EntryID, EntryID ) const;
                std::vector< const Bound<T1, T2>* > getConflict( EntryID ) const;
                std::vector< std::set< const Bound<T1, T2>* > > getConflictsFrom( EntryID ) const;
                void updateBasicAssignments( size_t, const Value<T1>& );
                void pivot( EntryID );
                void update( bool downwards, EntryID, std::vector<Iterator>&, std::vector<Iterator>& );
                void insert( const T2&, Iterator&, bool, Iterator&, bool );
                #ifdef LRA_REFINEMENT
                void rowRefinement( Variable<T1, T2>* );
                #endif
                size_t unboundedVariables( const Variable<T1,T2>& ) const;
                size_t checkCorrectness() const;
                bool rowCorrect( size_t _rowNumber ) const;
                #ifdef LRA_CUTS_FROM_PROOFS
                bool isDefining( size_t, std::vector<size_t>&, std::vector<T2>&, T2&, T2& ) const;
                bool isDefining_Easy( std::vector<size_t>&, size_t );
                bool isDiagonal( size_t, std::vector<size_t>& );
                size_t position_DC( size_t, std::vector<size_t>& );
                size_t revert_diagonals( size_t, std::vector<size_t>& );
                void invertColumn( size_t );
                void addColumns( size_t, size_t, T2 );
                void multiplyRow( size_t, T2 );
                T2 Scalar_Product( Tableau<T2>&, Tableau<T2>&, size_t, size_t, T, std::vector<size_t>&, std::vector<size_t>& );
                void calculate_hermite_normalform( std::vector<size_t>& );
                void invert_HNF_Matrix( std::vector<size_t> );
                bool create_cut_from_proof( Tableau<T2>&, Tableau<T2>&, size_t&, T2&, std::vector<T2>&, std::vector<bool>&, smtrat::Polynomial&, std::vector<size_t>&, std::vector<size_t>&, Bound<T1, T2>*&);
                #endif
                #ifdef LRA_GOMORY_CUTS
                const smtrat::Constraint* gomoryCut( const T2&, size_t, std::vector<const smtrat::Constraint*>& );
                #endif
                void printHeap( std::ostream& = std::cout, int = 30, const std::string = "" ) const;
                void printEntry( EntryID, std::ostream& = std::cout, int = 20 ) const;
                void printVariables( bool = true, std::ostream& = std::cout, const std::string = "" ) const;
                #ifdef LRA_REFINEMENT
                void printLearnedBounds( const std::string = "", std::ostream& = std::cout ) const;
                #endif
                void print( std::ostream& = std::cout, int = 28, const std::string = "" ) const;

        };

        template<typename T1, typename T2>
        Tableau<T1,T2>::Tableau( smtrat::Formula::iterator _defaultBoundPosition ):
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
            mConflictingRows()
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
            while( !mRows.empty() )
            {
                Variable<T1,T2>* varToRemove = mRows.back();
                mRows.pop_back();
                delete varToRemove;
            }
            while( !mColumns.empty() )
            {
                Variable<T1,T2>* varToRemove = mColumns.back();
                mColumns.pop_back();
                delete varToRemove;
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
//            std::cout << "newBasicVariable" << std::endl;
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
//                std::cout << "non basic variable is:" << std::endl;
//                nonBasic->print();
//                std::cout << std::endl;
//                std::cout << "with coefficient: " << T2( carl::getNum( (*term)->coeff() ) ) << std::endl;
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
//            std::cout << "activate " << std::endl;
//            _var->print();
//            std::cout << std::endl;
//            std::cout << "with factor " << _var->factor() << std::endl;
//            printHeap();
//            print();
            std::map<size_t,T2> coeffs;
            for( auto lravarCoeffPair = _var->positionInNonActives()->begin(); lravarCoeffPair != _var->positionInNonActives()->end(); ++lravarCoeffPair )
            {
                Variable<T1, T2>* lravar = lravarCoeffPair->first;
                if( lravar->isBasic() )
                {
                    if( !lravar->isActive() && !lravar->isOriginal() )
                    {
//                        std::cout << "non-active basic variable: " << std::endl;
//                        lravar->print();
//                        std::cout << std::endl;
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
//                        std::cout << "lravar->factor() = " << lravar->factor() << std::endl;
//                        std::cout << "lravarCoeffPair->second = " << lravarCoeffPair->second << std::endl;
//                        std::cout << "ca = " << ca << std::endl;
//                        std::cout << "cb = " << cb << std::endl;
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
//                            std::cout << "update at row position " << iter->first << " being " << iter->second << " with " << cb << std::endl;
                            iter->second *= cb;
//                            std::cout << "results in " << iter->second << std::endl;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
//                            std::cout << "update coefficient of ";
//                            iterB->first->print();
//                            std::cout << " having coefficient " << iterB->second << " with " << cb << std::endl;
                            iterB->second *= cb;
                        }
                        #endif
                        for( auto lravarCoeffPairB = lravar->positionInNonActives()->begin(); lravarCoeffPairB != lravar->positionInNonActives()->end(); ++lravarCoeffPairB )
                        {
//                            std::cout << "take variable under consideration: " << std::endl;
//                            lravarCoeffPairB->first->print();
//                            std::cout << std::endl;
//                            
//                            std::cout << "with coefficient: " << ca*lravarCoeffPairB->second << std::endl;
                            _var->positionInNonActives()->emplace_back( lravarCoeffPairB->first, ca*lravarCoeffPairB->second );
                        }
                    }
                    else
                    {
//                        std::cout << "active basic variable: " << std::endl;
//                        lravar->print();
//                        std::cout << std::endl;
                        #ifdef LRA_NO_DIVISION
                        T2 l = carl::lcm( lravarCoeffPair->second, lravar->factor() );
                        assert( l > 0 );
                        if( lravarCoeffPair->second < 0 && lravar->factor() < 0 )
                            l *= T2( -1 );
                        T2 ca = carl::div( l, lravar->factor() );
                        T2 cb = carl::div( l, lravarCoeffPair->second );
//                        std::cout << "lravar->factor() = " << lravar->factor() << std::endl;
//                        std::cout << "lravarCoeffPair->second = " << lravarCoeffPair->second << std::endl;
//                        std::cout << "ca = " << ca << std::endl;
//                        std::cout << "cb = " << cb << std::endl;
                        _var->rFactor() *= cb;
                        for( auto iter = coeffs.begin(); iter != coeffs.end(); ++iter )
                        {
//                            std::cout << "update at row position " << iter->first << " being " << iter->second << " with " << cb << std::endl;
                            iter->second *= cb;
//                            std::cout << "results in " << iter->second << std::endl;
                        }
                        auto iterB = lravarCoeffPair;
                        ++iterB;
                        for( ; iterB != _var->positionInNonActives()->end(); ++iterB )
                        {
//                            std::cout << "update coefficient of ";
//                            iterB->first->print();
//                            std::cout << " having coefficient " << iterB->second << " with " << cb << std::endl;
                            iterB->second *= cb;
                        }
                        #endif
                        Iterator rowIter = Iterator( lravar->startEntry(), mpEntries );
                        while( true )
                        {
//                            std::cout << "add coefficient: " << ca*(*rowIter).content() << std::endl;
//                            std::cout << "to variable: " << std::endl;
//                            (*rowIter).columnVar()->print();
//                            std::cout << std::endl;
                            coeffs[(*rowIter).columnVar()->position()] += ca*(*rowIter).content();
                            if( rowIter.hEnd( false ) ) break;
                            else rowIter.hMove( false );
                        }
                    }
                }
                else
                {
//                    std::cout << "non-basic variable: " << std::endl;
//                    lravar->print();
//                    std::cout << std::endl;
//                    std::cout << "add coefficient: " << lravarCoeffPair->second << std::endl;
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
//                printHeap();
//                print();
//                printVariables();
//            if( checkCorrectness() != mRows.size() )
//            {
//                exit( 777 );
//            }
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
//            std::cout << "deactivate " << std::endl;
//            _var->print();
//            printHeap();
//            print();
//            std::cout << std::endl;
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
//            printHeap();
//            print();
        }
        
        /**
         *
         * @return
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::compressRows()
        {
            if( mRowsCompressed ) return;
//            std::cout << __func__ << std::endl;
//            print();
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
                    //mRows[curPos] = NULL;
                    emptyPositions.push_back( curPos );
                }
                ++curPos;
            }
            mRows.resize( mRows.size() - emptyPositions.size() );
            mRowsCompressed = true;
//            print();
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
                #ifdef LRA_USE_OCCURENCE_STRATEGY
                size_t smallestRowSize = mWidth;
                assert( mRows.size() >= mUnusedRows.size() );
                size_t smallestColumnSize = mRows.size()-mUnusedRows.size();
                #endif
                EntryID beginOfBestRow = LAST_ENTRY_ID;
                EntryID beginOfFirstConflictRow = LAST_ENTRY_ID;
                *mpTheta = Value<T1>( 0 );
                Value<T1> conflictTheta =  Value<T1>( 0 );
                #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                std::vector<Variable<T1,T2>*>& rowsToConsider = mConflictingRows.empty() ? mRows : mConflictingRows;
                Variable<T1,T2>* bestVar = NULL;
                #else
                std::vector<Variable<T1,T2>*>& rowsToConsider = mRows;
                #endif 
                for( Variable<T1,T2>* basicVar : rowsToConsider )
                {
                    assert( basicVar != NULL );
                    Value<T1> theta = Value<T1>();
                    // TODO: Check first whether it is conflicting its bounds and set theta accordingly for heuristics
                    std::pair<EntryID,bool> result = isSuitable( *basicVar, theta );
                    if( !result.second )
                    {
                        // Found a conflicting row.
                        if( beginOfFirstConflictRow == LAST_ENTRY_ID )
                        {
                            conflictTheta = theta;
                            beginOfFirstConflictRow = result.first;
                            #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                            bestVar = basicVar;
                            #endif
                            break;
                        }
                    }
                    else if( result.first != LAST_ENTRY_ID )
                    {
                        #ifdef LRA_USE_THETA_STRATEGY
                        if( beginOfBestRow == LAST_ENTRY_ID || carl::abs( theta.mainPart() ) > carl::abs( mpTheta->mainPart() ) )
                        {
                            beginOfBestRow = result.first;
                            *mpTheta = theta;
                            #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                            bestVar = basicVar;
                            #endif
                        }
                        #endif
                        #ifdef LRA_USE_OCCURENCE_STRATEGY
                        if( basicVar->size() < smallestRowSize )
                        {
                            // Found a better pivoting element.
                            smallestRowSize = basicVar->size();
                            smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                            beginOfBestRow = result.first;
                            *mpTheta = theta;
                            #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                            bestVar = basicVar;
                            #endif
                        }
                        else if( basicVar->size() == smallestRowSize
                                 && mColumns[(*mpEntries)[result.first].columnNumber()].mSize < smallestColumnSize )
                        {
                            // Found a better pivoting element.
                            smallestColumnSize = mColumns[(*mpEntries)[result.first].columnNumber()].mSize;
                            beginOfBestRow = result.first;
                            *mpTheta = theta;
                            #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                            bestVar = basicVar;
                            #endif
                        }
                        #endif
                    }
                }
                if( beginOfBestRow == LAST_ENTRY_ID && beginOfFirstConflictRow != LAST_ENTRY_ID )
                {
                    // Found a conflict
                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                    mConflictingRows.clear();
                    #endif
                    return std::pair<EntryID,bool>( beginOfFirstConflictRow, false );
                }
                else if( beginOfBestRow != LAST_ENTRY_ID )
                {
                    // The best pivoting element found
                    #ifdef LRA_LOCAL_CONFLICT_DIRECTED
                    if( !mConflictingRows.empty() )
                    {
                        auto iter = mConflictingRows.begin();
                        for( ; iter != mConflictingRows.end(); ++iter )
                        {
                            if( (*iter) == bestVar ) break;
                        }
                        mConflictingRows.erase( iter );
                    }
                    #endif
                    return std::pair<EntryID,bool>( beginOfBestRow, true );
                }
                else
                {
                    // Found no pivoting element, that is no variable violates its bounds.
                    if( !mConflictingRows.empty() )
                    {
                        mConflictingRows.clear();
                        return nextPivotingElement();
                    }
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
                    std::pair<EntryID,bool> result = isSuitable( *basicVar, *mpTheta );
                    if( !result.second )
                    {
                        // Found a conflicting row.
                        return std::pair<EntryID,bool>( result.first, false );
                    }
                    else if( result.first != LAST_ENTRY_ID )
                    {
                        // Found a pivoting element
                        return std::pair<EntryID,bool>( result.first, true );
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
        std::pair<EntryID,bool> Tableau<T1,T2>::isSuitable( const Variable<T1, T2>& _basicVar, Value<T1>& _theta ) const
        {
            EntryID bestEntry = LAST_ENTRY_ID;
            const Bound<T1, T2>& basicVarSupremum = _basicVar.supremum();
            const Value<T1>& basicVarAssignment = _basicVar.assignment();
            const Bound<T1, T2>& basicVarInfimum = _basicVar.infimum();
            EntryID rowStartEntry = _basicVar.startEntry();
            // Upper bound is violated
            if( basicVarSupremum < basicVarAssignment ) // TODO: you could know this beforehand, so make two methods for case distinction or add a bool template
            {
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
                                #ifdef LRA_NO_DIVISION
                                _theta = ((basicVarSupremum.limit() - basicVarAssignment)*_basicVar.factor())/(*rowIter).content();
                                #else
                                _theta = (basicVarSupremum.limit() - basicVarAssignment)/(*rowIter).content();
                                #endif
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
                                #ifdef LRA_NO_DIVISION
                                _theta = ((basicVarSupremum.limit() - basicVarAssignment)*_basicVar.factor())/(*rowIter).content();
                                #else
                                _theta = (basicVarSupremum.limit() - basicVarAssignment)/(*rowIter).content();
                                #endif
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            _theta = basicVarAssignment - basicVarSupremum.limit();
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
            else if( basicVarInfimum > basicVarAssignment )
            {
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
                                #ifdef LRA_NO_DIVISION
                                _theta = ((basicVarInfimum.limit() - basicVarAssignment)*_basicVar.factor())/(*rowIter).content();
                                #else
                                _theta = (basicVarInfimum.limit() - basicVarAssignment)/(*rowIter).content();
                                #endif
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
                                #ifdef LRA_NO_DIVISION
                                _theta = ((basicVarInfimum.limit() - basicVarAssignment)*_basicVar.factor())/(*rowIter).content();
                                #else
                                _theta = (basicVarInfimum.limit() - basicVarAssignment)/(*rowIter).content();
                                #endif
                                bestEntry = rowIter.entryID();
                            }
                        }
                    }
                    if( rowIter.hEnd( false ) )
                    {
                        if( bestEntry == LAST_ENTRY_ID )
                        {
                            _theta = basicVarInfimum.limit() - basicVarAssignment;
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
            size_t valueA = unboundedVariables( isBetterNbVar );
            size_t valueB = unboundedVariables( thanColumnNbVar );
            if( valueA > valueB ) return true;
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
            for( Variable<T1,T2>* rowElement : mRows )
            {
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
//            std::cout << "pivot" << std::endl;
//                printHeap();
//                print();
//                printEntry( _pivotingElement );
//                std::cout << std::endl;
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
//                printEntry( colIter.entryID() );
//                std::cout << std::endl;
                (*colIter).setColumnVar( rowVar );
                if( colIter.vEnd( false ) )
                    break;
                colIter.vMove( false );
            }
//            printHeap();
            while( !iterTemp.hEnd( true ) )
            {
                iterTemp.hMove( true );
//                printEntry( iterTemp.entryID() );
//                std::cout << std::endl;
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowLeftSide.push_back( iterTemp );
            }
//            printHeap();
//            std::cout << "blaaac" << std::endl;
            // Then the column with ** right to the pivoting column until the rightmost column with **.
            std::vector<Iterator> pivotingRowRightSide = std::vector<Iterator>();
            iterTemp = Iterator( _pivotingElement, mpEntries );
            while( !iterTemp.hEnd( false ) )
            {
                iterTemp.hMove( false );
//                printEntry( iterTemp.entryID() );
//                std::cout << std::endl;
                (*iterTemp).setRowVar( columnVar );
                #ifdef LRA_NO_DIVISION
                (*iterTemp).rContent() = -(*iterTemp).content();
                #else
                (*iterTemp).rContent() /= -pivotContent;
                #endif
                pivotingRowRightSide.push_back( iterTemp );
            }
//            printHeap();
//            std::cout << "blaaaa" << std::endl;
            // Swap the variables
            mRows[rowVar->position()] = columnVar;
            mColumns[columnVar->position()] = rowVar;
            // Update the assignments of the pivoting variables
            #ifdef LRA_NO_DIVISION
            rowVar->rAssignment() += ((*mpTheta) * pivotContent) / rowVar->factor();
            #else
            rowVar->rAssignment() += (*mpTheta) * pivotContent;
            #endif
            assert( rowVar->supremum() > rowVar->assignment() || rowVar->supremum() == rowVar->assignment() );
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
                rowRefinement( columnVar ); // Note, we have swapped the variables, so the current basic var is now corresponding what we have stored in columnVar.
            }
            #endif
//            printHeap();
//            print();
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
//            if( checkCorrectness() != mRows.size() )
//            {
//                std::cout << "row number: " << checkCorrectness() << std::endl;
//                printHeap();
//                print();
//            }
            assert( checkCorrectness() == mRows.size() );
        }

        /**
         *
         * @param _pivotingElement
         * @param _pivotingRow
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::update( bool downwards, EntryID _pivotingElement, std::vector<Iterator>& _pivotingRowLeftSide, std::vector<Iterator>& _pivotingRowRightSide )
        {
            std::vector<Iterator> leftColumnIters = std::vector<Iterator>( _pivotingRowLeftSide );
            std::vector<Iterator> rightColumnIters = std::vector<Iterator>( _pivotingRowRightSide );
            Iterator pivotingColumnIter = Iterator( _pivotingElement, mpEntries );
            #ifdef LRA_NO_DIVISION
            const T2& pivotingRowFactor = (*mpEntries)[_pivotingElement].rowVar()->factor();
            #endif
            while( true )
            {
                if( !pivotingColumnIter.vEnd( downwards ) )
                {
                    pivotingColumnIter.vMove( downwards );
                }
                else
                {
                    break;
                }
//                std::cout << "entry in pivoting column: ";
//                printEntry(pivotingColumnIter.entryID());
//                std::cout << std::endl;
                // Update the assignment of the basic variable corresponding to this row
                Variable<T1,T2>& currBasicVar = *((*pivotingColumnIter).rowVar());
                #ifdef LRA_NO_DIVISION
                currBasicVar.rAssignment() += ((*mpTheta) * (*pivotingColumnIter).content())/currBasicVar.factor();
                #else
                currBasicVar.rAssignment() += (*mpTheta) * (*pivotingColumnIter).content();
                #endif
                // Update the row
                Iterator currentRowIter = pivotingColumnIter;
//                std::cout << "entry in current row: ";
//                printEntry(currentRowIter.entryID());
//                std::cout << std::endl;
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
//                    std::cout << "entry in current column: ";
//                    printEntry((*currentColumnIter).entryID());
//                    std::cout << std::endl;
                    assert( pivotingRowIter != _pivotingRowLeftSide.end() );
                    while( (downwards && !(*currentColumnIter).vEnd( downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position()) 
                           || (!downwards && !(*currentColumnIter).vEnd( downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( downwards );
                    }
//                    std::cout << "entry in current row: ";
//                    printEntry(currentRowIter.entryID());
//                    std::cout << std::endl;
                    while( !currentRowIter.hEnd( true ) && (*currentRowIter).columnVar()->position() > (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( true );
                    }
//                    std::cout << "entry in current row: ";
//                    printEntry(currentRowIter.entryID());
//                    std::cout << std::endl;
                    #ifdef LRA_NO_DIVISION
                    insert( ca * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, downwards );
                    #else
                    insert( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, true, *currentColumnIter, downwards );
                    #endif
                    ++pivotingRowIter;
                }
                currentRowIter = pivotingColumnIter;
                pivotingRowIter = _pivotingRowRightSide.begin();
                for( auto currentColumnIter = rightColumnIters.begin(); currentColumnIter != rightColumnIters.end(); ++currentColumnIter )
                {
//                    std::cout << "entry in current column: ";
//                    printEntry((*currentColumnIter).entryID());
//                    std::cout << std::endl;
                    assert( pivotingRowIter != _pivotingRowRightSide.end() );
                    while( (downwards && !(*currentColumnIter).vEnd( downwards ) && (**currentColumnIter).rowVar()->position() < (*pivotingColumnIter).rowVar()->position())
                           || (!downwards && !(*currentColumnIter).vEnd( downwards ) && (**currentColumnIter).rowVar()->position() > (*pivotingColumnIter).rowVar()->position()) )
                    {
                        (*currentColumnIter).vMove( downwards );
                    }
                    while( !currentRowIter.hEnd( false ) && (*currentRowIter).columnVar()->position() < (**currentColumnIter).columnVar()->position() )
                    {
                        currentRowIter.hMove( false );
                    }
//                    std::cout << "entry in current row: ";
//                    printEntry(currentRowIter.entryID());
//                    std::cout << std::endl;
                    #ifdef LRA_NO_DIVISION
                    insert( ca * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, downwards );
                    #else
                    insert( (*pivotingColumnIter).content() * (**pivotingRowIter).content(), currentRowIter, false, *currentColumnIter, downwards );
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
        
        template<typename T1, typename T2>
        void Tableau<T1,T2>::insert( const T2& _content, Iterator& _horiPos, bool _leftwards, Iterator& _vertPos, bool _downwards )
        {
//            std::cout << "add " << _content;
//            std::cout << (_leftwards ? " leftwards" : " rightwards") << " from (" << (*_horiPos).rowVar()->position() << ", " << (*_horiPos).columnVar()->position() << ")";
//            std::cout << (_downwards ? " downwards" : " upwards") << " from (" << (*_vertPos).rowVar()->position() << ", " << (*_vertPos).columnVar()->position() << ")" << std::endl;
            
//            printHeap();
//            print();
            if( _horiPos == _vertPos )
            {
//                std::cout << "bla1" << std::endl;
                // Entry already exists, so update it only and maybe remove it.
                T2& currentRowContent = (*_horiPos).rContent();
                #ifdef LRA_NO_DIVISION
                currentRowContent += _content;
                #else
                currentRowContent += _content;
                #endif
                if( currentRowContent == 0 )
                {
                    EntryID toRemove = _horiPos.entryID();
                    _vertPos.vMove( !_downwards );
                    _horiPos.hMove( !_leftwards );
                    removeEntry( toRemove );
                }
            }
            else
            {
//                std::cout << "bla2" << std::endl;
                EntryID entryID = newTableauEntry( _content );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                // Set the position.
                Variable<T1,T2>* basicVar = (*mpEntries)[_horiPos.entryID()].rowVar();
                Variable<T1,T2>* nonbasicVar = (*mpEntries)[_vertPos.entryID()].columnVar();
                entry.setRowVar( basicVar );
                entry.setColumnVar( nonbasicVar );
                if( (_downwards && (*_vertPos).rowVar()->position() > (*_horiPos).rowVar()->position())
                    || (!_downwards && (*_vertPos).rowVar()->position() < (*_horiPos).rowVar()->position()) )
                {
//                std::cout << "bla3" << std::endl;
                    // Entry vertically between two entries.
                    EntryID upperEntryID = (*_vertPos).vNext( !_downwards );
                    if( upperEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[upperEntryID].setVNext( _downwards, entryID );
                    }
                    (*_vertPos).setVNext( !_downwards, entryID );
                    entry.setVNext( !_downwards, upperEntryID );
                    entry.setVNext( _downwards, _vertPos.entryID() );
                }
                else
                {
//                std::cout << "bla4" << std::endl;
                    // Entry will be the lowest in this column.
                    (*_vertPos).setVNext( _downwards, entryID );
                    entry.setVNext( !_downwards, _vertPos.entryID() );
                    entry.setVNext( _downwards, LAST_ENTRY_ID );
                    if( _downwards )
                        nonbasicVar->rStartEntry() = entryID;
                }
                if( (_leftwards && (*_horiPos).columnVar()->position() < (*_vertPos).columnVar()->position())
                    || (!_leftwards && (*_horiPos).columnVar()->position() > (*_vertPos).columnVar()->position()) )
                {
//                std::cout << "bla5" << std::endl;
                    // Entry horizontally between two entries.
                    EntryID rightEntryID = (*_horiPos).hNext( !_leftwards );
                    if( rightEntryID != LAST_ENTRY_ID )
                    {
                        (*mpEntries)[rightEntryID].setHNext( _leftwards, entryID );
                    }
                    (*_horiPos).setHNext( !_leftwards, entryID );
                    entry.setHNext( !_leftwards, rightEntryID );
                    entry.setHNext( _leftwards, _horiPos.entryID() );
                }
                else
                {
//                std::cout << "bla6" << std::endl;
                    // Entry will be the leftmost in this row.
                    (*_horiPos).setHNext( _leftwards, entryID );
                    entry.setHNext( !_leftwards, _horiPos.entryID() );
                    entry.setHNext( _leftwards, LAST_ENTRY_ID );
                    if( _leftwards )
                        basicVar->rStartEntry() = entryID;
                }
                // Set the content of the entry.
                ++(basicVar->rSize());
                ++(nonbasicVar->rSize());
            }
//            printHeap();
//            print();
        }

        #ifdef LRA_REFINEMENT
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
                    learnedBound.premise = uPremise;
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
                        const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel );
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
                            delete insertionResult.first->second.premise;
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
                    learnedBound.premise = lPremise;
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
                        const smtrat::Constraint* constraint = smtrat::Formula::newConstraint( lhs, rel );
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
                            delete insertionResult.first->second.premise;
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
        size_t Tableau<T1,T2>::unboundedVariables( const Variable<T1,T2>& _var ) const
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
                            ++unboundedVars;
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
                            ++unboundedVars;
                        if( columnEntry.vEnd( false ) )
                            break;
                        columnEntry.vMove( false );
                    }
                }
                return unboundedVars;
            }
            return true;
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
//            std::cout << "bla1" << std::endl;
            size_t numOfRowElements = 0;
            smtrat::Polynomial sumOfNonbasics = smtrat::ZERO_POLYNOMIAL;
//            std::cout << "sumOfNonbasics = " << sumOfNonbasics << std::endl;
            Iterator rowEntry = Iterator( mRows[_rowNumber]->startEntry(), mpEntries );
            while( !rowEntry.hEnd( false ) )
            {
                sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
//            std::cout << "sumOfNonbasics += " << ((*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() )) << std::endl;
//            std::cout << "sumOfNonbasics = " << sumOfNonbasics << std::endl;
                ++numOfRowElements;
                rowEntry.hMove( false );
            }
            ++numOfRowElements;
            if( numOfRowElements != mRows[_rowNumber]->size() )
            {
//                std::cout << "bla2" << std::endl;
                return false;
            }
            sumOfNonbasics += (*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() );
//            std::cout << "sumOfNonbasics += " << ((*((*rowEntry).columnVar()->pExpression())) * smtrat::Polynomial( (*rowEntry).content() )) << std::endl;
//            std::cout << "sumOfNonbasics = " << sumOfNonbasics << std::endl;
            #ifdef LRA_NO_DIVISION
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::Polynomial( mRows[_rowNumber]->factor() ) * smtrat::MINUS_ONE_POLYNOMIAL;
//            std::cout << "sumOfNonbasics += " << ((*mRows[_rowNumber]->pExpression()) * smtrat::Polynomial( mRows[_rowNumber]->factor() ) * smtrat::MINUS_ONE_POLYNOMIAL) << std::endl;
//            std::cout << "sumOfNonbasics = " << sumOfNonbasics << std::endl;
            #else
            sumOfNonbasics += (*mRows[_rowNumber]->pExpression()) * smtrat::MINUS_ONE_POLYNOMIAL;
            #endif
//            std::cout << "bla3" << std::endl;
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
        bool Tableau<T1,T2>::isDefining( size_t row_index, std::vector<size_t>& _variables, std::vector<T2>& _coefficients, T2& _lcmOfCoeffDenoms, T2& max_value ) const
        {
            const Variable<T1, T2>& basic_var = *mRows.at(row_index).mName;
            Iterator row_iterator = Iterator( mRows.at(row_index).mStartEntry, mpEntries );
            if( basic_var.infimum() == basic_var.assignment() || basic_var.supremum() == basic_var.assignment() )
            {
                /*
                 * The row represents a DC. Collect the nonbasics and the referring coefficients.
                 */
                while( true )
                {
                    _variables.push_back( (*row_iterator).columnNumber() );
                    _coefficients.push_back( (*row_iterator).content() );
                    _lcmOfCoeffDenoms = carl::lcm( _lcmOfCoeffDenoms, (*row_iterator).content().denom() );
                    if( !row_iterator.horiEnd( false ) )
                    {
                        row_iterator.hNext( false );
                    }
                    else
                    {
                        break;
                    }
                }
                return true;
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
                    if( !row_iterator.horiEnd( false ) )
                    {
                        row_iterator.hNext( false );
                    }
                    else
                    {
                        break;
                    }                    
                }                
            }
            return false;
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
            Iterator column_iterator = Iterator(mColumns.at(column_index).mStartEntry, mpEntries);   
            while(true)
            {
                (*mpEntries)[column_iterator.entryID()].rContent() = (-1)*(((*mpEntries)[column_iterator.entryID()].rContent()).content());
                if(!column_iterator.vertEnd( false ))
                {
                    column_iterator.vNext( false );            
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
            Iterator columnA_iterator = Iterator(mColumns.at(columnA_index).mStartEntry, mpEntries);
            Iterator columnB_iterator = Iterator(mColumns.at(columnB_index).mStartEntry, mpEntries);
                
            while(true)
            {
            /* 
             * Make columnA_iterator and columnB_iterator neighbors. 
             */ 
            while((*columnA_iterator).rowNumber() > (*columnB_iterator).rowNumber() && !columnA_iterator.vertEnd( false ))
            {
                columnA_iterator.vNext( false );
            }    
            EntryID ID1_to_be_Fixed,ID2_to_be_Fixed;            
            if((*columnA_iterator).rowNumber() == (*columnB_iterator).rowNumber())
            {
                T2 content = T2(((*columnA_iterator).content().content())+((multiple.content())*((*columnB_iterator).content().content())));  
                if(content == 0)
                {
                    EntryID to_delete = columnA_iterator.entryID();
                    if(!columnA_iterator.vertEnd( false ))
                    {                        
                        columnA_iterator.vNext( false );
                    }    
                    removeEntry(to_delete);                
                 }                
                 else
                 {
                    (*columnA_iterator).rContent() = content;           
                 }    
              }
              else if((*columnA_iterator).rowNumber() < (*columnB_iterator).rowNumber()) 
              {
                  /*
                   * A new entry has to be created under the position of columnA_iterator
                   * and sideways to column_B_iterator.
                   */   
                  EntryID entryID = newTableauEntry(T2(((multiple.content())*((*columnB_iterator).content().content()))));
                  TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                  TableauEntry<T1,T2>& entry_down = (*mpEntries)[(*columnA_iterator).vNext( true )];   
                  EntryID down = (*columnA_iterator).vNext( true );
                  entry.setColumnNumber((*columnA_iterator).columnNumber());
                  entry.setRowNumber((*columnB_iterator).rowNumber());
                  entry.setVertNext( true,down);
                  entry.setVertNext( false,columnA_iterator.entryID());
                  entry_down.setVertNext( false,entryID);
                  (*columnA_iterator).setVertNext( true,entryID);
                  TableauHead& columnHead = mColumns[entry.columnNumber()];
                  ++columnHead.mSize;
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if((*row_iterator).columnNumber() > entry.columnNumber())
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */
                      while((*row_iterator).columnNumber() > entry.columnNumber() && !row_iterator.horiEnd( true ))
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hNext( true ); 
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if((*row_iterator).columnNumber() > entry.columnNumber() && row_iterator.horiEnd( true ))
                      {                          
                          (*mpEntries)[entryID].setHoriNext( true,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHoriNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( true,entryID);
                          TableauHead& rowHead = mRows[(*columnB_iterator).rowNumber()];
                          rowHead.mStartEntry = entryID;
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHoriNext( true,entryID);
                          (*mpEntries)[entryID].setHoriNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHoriNext( false,ID1_to_be_Fixed);
                      }
                  }    
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while((*row_iterator).columnNumber() < entry.columnNumber() && !row_iterator.horiEnd( false ))
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hNext( false );
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if((*row_iterator).columnNumber() < entry.columnNumber() && row_iterator.horiEnd( false ))
                      {
                          (*mpEntries)[entryID].setHoriNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHoriNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHoriNext( false,entryID);
                          (*mpEntries)[entryID].setHoriNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHoriNext( true,ID1_to_be_Fixed);
                      }
                  } 
                  TableauHead& rowHead = mRows[entry.rowNumber()];
                  ++rowHead.mSize;                      
                  if(columnHead.mStartEntry == columnA_iterator.entryID())
                  {
                      columnHead.mStartEntry = entryID;
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
                  entry.setColumnNumber((*columnA_iterator).columnNumber());
                  entry.setRowNumber((*columnB_iterator).rowNumber());
                  entry.setVertNext( true,columnA_iterator.entryID());
                  entry.setVertNext( false,LAST_ENTRY_ID);
                  (*columnA_iterator).setVertNext( false,entryID);
                  TableauHead& columnHead = mColumns[entry.columnNumber()];
                  ++columnHead.mSize;
                  Iterator row_iterator = Iterator(columnB_iterator.entryID(), mpEntries);
                  ID2_to_be_Fixed = row_iterator.entryID();
                  if((*row_iterator).columnNumber() > entry.columnNumber())
                  {
                      /*
                       * The new entry is left from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while((*row_iterator).columnNumber() > entry.columnNumber() && !row_iterator.horiEnd( true ))
                      {
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hNext( true );                     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if((*row_iterator).columnNumber() > entry.columnNumber() && row_iterator.horiEnd( true ))
                      {
                          (*mpEntries)[entryID].setHoriNext( true,LAST_ENTRY_ID);
                          (*mpEntries)[entryID].setHoriNext( false,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( true,entryID);
                          TableauHead& rowHead = mRows[(*columnB_iterator).rowNumber()];
                          rowHead.mStartEntry = entryID;                          
                      }                     
                      else
                      {
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( false,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHoriNext( true,entryID);
                          (*mpEntries)[entryID].setHoriNext( true,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHoriNext( false,ID1_to_be_Fixed);
                      }  
                  }  
                  else
                  {
                      /*
                       * The new entry is right from the added entry.
                       * Search for the entries which have to be modified.
                       */                      
                      while((*row_iterator).columnNumber() < entry.columnNumber() && !row_iterator.horiEnd( false ))
                      {                             
                          ID1_to_be_Fixed = row_iterator.entryID();
                          row_iterator.hNext( false );     
                          ID2_to_be_Fixed = row_iterator.entryID();
                      }
                      if((*row_iterator).columnNumber() < entry.columnNumber() && row_iterator.horiEnd( false ))
                      {
                          (*mpEntries)[entryID].setHoriNext( false,LAST_ENTRY_ID);  
                          (*mpEntries)[entryID].setHoriNext( true,ID2_to_be_Fixed);
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( false,entryID);
                      }    
                      else
                      {                          
                          (*mpEntries)[ID2_to_be_Fixed].setHoriNext( true,entryID);
                          (*mpEntries)[ID1_to_be_Fixed].setHoriNext( false,entryID);
                          (*mpEntries)[entryID].setHoriNext( false,ID2_to_be_Fixed); 
                          (*mpEntries)[entryID].setHoriNext( true,ID1_to_be_Fixed);
                      }                      
                  }   
               TableauHead& rowHead = mRows[entry.rowNumber()];
               ++rowHead.mSize;                  
               }
               if(!columnB_iterator.vertEnd( false ))
               {
                   columnB_iterator.vNext( false );
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
            Iterator row_iterator = Iterator(mRows.at(row_index).mStartEntry, mpEntries);
            while(true)
            { 
                T2 content = T2(((*row_iterator).content().content())*(multiple.content()));
                (*row_iterator).rContent() = content;
                if(!row_iterator.horiEnd( false ))
                {
                    row_iterator.hNext( false );
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
        T2 Tableau<T1,T2>::Scalar_Product(Tableau<T2>& A, Tableau<T2>& B,size_t rowA, size_t columnB, T2 lcm,std::vector<size_t>& diagonals,std::vector<size_t>& dc_positions) 
        {
            Iterator rowA_iterator = Iterator(A.mRows.at(rowA).mStartEntry,A.mpEntries);
            T2 result = T2(0);
            while(true)
            {
                Iterator columnB_iterator = Iterator(B.mColumns.at(columnB).mStartEntry,B.mpEntries);
                size_t actual_column = revert_diagonals((*rowA_iterator).columnNumber(),diagonals); 
                while(true)
                {
                    if(actual_column == position_DC((*columnB_iterator).rowNumber(),dc_positions))
                    {
                        result += (*rowA_iterator).content()*(*columnB_iterator).content()*lcm;
                        break;
                    }
                    if(columnB_iterator.vertEnd( false ))
                    {
                        break;
                    }
                    else
                    {
                        columnB_iterator.vNext( false );
                    }
                }    
                if(rowA_iterator.horiEnd( false ))
                {
                    break;
                }
                else
                {
                    rowA_iterator.hNext( false );
                }
            }
            #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
            std::cout << result << std::endl;
            #endif
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
            Iterator row_iterator = Iterator(mRows.at(0).mStartEntry, mpEntries);
            bool first_free;
            bool first_loop;
            bool just_deleted; 
            /*
             * Iterate through all rows in order to construct the HNF.
             */
            for(size_t i=0;i<mRows.size();i++)
            {
                size_t elim_pos=mColumns.size(),added_pos=mColumns.size();
                EntryID added_entry,elim_entry;
                T2 elim_content, added_content;     
                row_iterator = Iterator(mRows.at(i).mStartEntry, mpEntries);
                size_t number_of_entries = mRows.at(i).mSize;
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
                    Iterator diagonal_iterator = Iterator(mColumns.at(diagonals.at(j)).mStartEntry, mpEntries);
                    while((*diagonal_iterator).rowNumber() > i && !diagonal_iterator.vertEnd( false ))
                    {
                        diagonal_iterator.vNext( false );
                    }
                    if((*diagonal_iterator).rowNumber() != i)
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
                        if((*mpEntries)[added_entry].columnNumber() > (*mpEntries)[elim_entry].columnNumber())
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
                    Iterator help_iterator = Iterator(mRows.at(i).mStartEntry, mpEntries);
                    while(true)
                    {
                        if((*help_iterator).content() < 0 && !isDiagonal((*help_iterator).columnNumber(),diagonals))
                        {
                            invertColumn((*help_iterator).columnNumber());
                        }
                        if(!help_iterator.horiEnd( false ))
                        {
                            help_iterator.hNext( false );
                        }
                        else
                        {
                            break;
                        }
                    }
                    
                    while(elim_pos == added_pos)
                    { 
                        T2 content = (*mpEntries)[row_iterator.entryID()].content();
                        size_t column = (*mpEntries)[row_iterator.entryID()].columnNumber();   
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
                        if(elim_pos == added_pos && !row_iterator.horiEnd( false ))
                        {
                            row_iterator.hNext( false );  
                        }    
                    }
                    T2 floor_value = T2( elim_content / added_content ).floor();
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "floor_value = " << floor_value << std::endl;
                    std::cout << "added_content = " << added_content << std::endl;
                    std::cout << "elim_content = " << elim_content << std::endl;
                    std::cout << "T2((-1)*floor_value.content()*added_content.content()) = " << T2((-1)*floor_value.content()*added_content.content()) << std::endl;
                    #endif
                    addColumns(elim_pos,added_pos,T2((-1)*floor_value.content()));
                    #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                    std::cout << "Add " << (added_pos+1) << ". column to " << (elim_pos+1) << ". column:" << std::endl;
                    print();
                    #endif
                    number_of_entries = mRows.at(i).mSize; 
                    first_loop = false;
                    if(mod( elim_content, added_content ) == 0)
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
                    while(isDiagonal((*row_iterator).columnNumber(),diagonals))
                    {
                        row_iterator.hNext( false );                        
                    }
                    added_content = (*row_iterator).content();
                    added_pos = (*row_iterator).columnNumber();
                } 
                diagonals.at(i) = added_pos;                
                /*
                 *  Normalize row.
                 */
                row_iterator = Iterator(mRows.at(i).mStartEntry, mpEntries);
                while(true)
                {                  
                    if( ( (*row_iterator).columnNumber() != added_pos ) && ( isDiagonal((*row_iterator).columnNumber(),diagonals) ) && ( added_content <= carl::abs( (*row_iterator).content() ) ) )
                    {
                       /*
                        * The current entry has to be normalized because it´s
                        * in a diagonal column and greater or equal than the
                        * diagonal entry in the current row.
                        */
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        std::cout << "Normalize" << std::endl;
                        std::cout << (*mpEntries)[row_iterator.entryID()].columnNumber() << std::endl;
                        std::cout << diagonals.at(i) << std::endl;
                        #endif
                        T2 floor_value = T2( (*row_iterator).content() / added_content ).floor();
                        addColumns((*mpEntries)[row_iterator.entryID()].columnNumber(),
                                  diagonals.at(i),
                                  (-1)*(floor_value));
                        #ifdef LRA_DEBUG_CUTS_FROM_PROOFS
                        print();
                        #endif
                    }
                    if(!row_iterator.horiEnd( false ))
                    {
                        row_iterator.hNext( false ); 
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
        void Tableau<T1,T2>::invert_HNF_Matrix(std::vector<size_t> diagonals)
        {
            /*
             * Iterate through the tableau beginning in the the last
             * column which only contains one element.
             */            
            for(int i=mRows.size()-1;i>=0;--i)
            {
                /*
                 * Move the iterator to the diagonal element in the current column
                 * and calculate the new content for it.
                 */
                Iterator column_iterator = Iterator(mColumns.at(diagonals.at(i)).mStartEntry, mpEntries);  
                while(!column_iterator.vertEnd( false ))
                {
                    column_iterator.vNext( false );                    
                }
                (*column_iterator).rContent() = 1/(*column_iterator).content();
                bool entry_changed=false;
                /*
                 * Now change the other entries in the current column if necessary.
                 */
                if(!column_iterator.vertEnd( true ))
                {
                    column_iterator.vNext( true );
                    entry_changed = true;
                }
                if(entry_changed)
                {
                    while(true)
                    {
                        entry_changed = false;
                        size_t j = i + 1;
                        T2 new_value = T2(0);
                        while(j < mRows.size())
                        {
                            Iterator column_iterator2 = Iterator(mColumns.at(diagonals.at(j)).mStartEntry, mpEntries);
                            while((*column_iterator2).rowNumber() > (*column_iterator).rowNumber() && !column_iterator2.vertEnd( false ))
                            {
                                column_iterator2.vNext( false );
                            }
                            if((*column_iterator2).rowNumber() == (*column_iterator).rowNumber())
                            {
                                new_value -= (*column_iterator2).content();
                                entry_changed = true;
                            }
                            j++;
                        }
                        if(entry_changed)
                        {
                            (*column_iterator).rContent() = new_value;
                        }    
                        if(!column_iterator.vertEnd( true ))
                        {
                            column_iterator.vNext( true );
                        }
                        else
                        {
                            break;
                        }
                    }
                }
            }
        }
        
        /**
         * Checks whether a cut from proof can be constructed with the row with index row_index
         * in the DC_Tableau. 
         * 
         * @return true,    if the proof can be constructed.
         *         false,   otherwise   
         */
        template<typename T1, typename T2>
        bool Tableau<T1,T2>::create_cut_from_proof(Tableau<T2>& Inverted_Tableau, Tableau<T2>& DC_Tableau, size_t& row_index, T2& _lcm,std::vector<T2>& coefficients,std::vector<bool>& non_basics_proof, smtrat::Polynomial& cut,std::vector<size_t>& diagonals,std::vector<size_t>& dc_positions, Bound<T1, T2>*& upper_lower)
        {
            Value<T1> result = T2(0);
            Iterator row_iterator = Iterator(mRows.at(row_index).mStartEntry,mpEntries); 
            /*
             * Calculate H^(-1)*b 
             */
            size_t i;
            while(true)
            {
                i = revert_diagonals((*row_iterator).columnNumber(),diagonals);
                const Variable<T1, T2>& basic_var = *(DC_Tableau.mRows)[dc_positions.at(i)].mName;
                const Value<T1>& basic_var_assignment = basic_var.assignment();
                result += basic_var_assignment * (*row_iterator).content() * _lcm;                    
                if(row_iterator.horiEnd( false ))
                {
                    break;
                }
                else
                {
                    row_iterator.hNext( false );
                }                
            }
            if( !result.mainPart().isInteger() )
            {
               // Calculate the lcm of all entries in the row with index row_index in the DC_Tableau
               Iterator row_iterator = Iterator(DC_Tableau.mRows.at(dc_positions.at(row_index)).mStartEntry,DC_Tableau.mpEntries);
               T2 lcm_row = T2(1);
               while(true)
               {
                   _lcm  = carl::lcm( _lcm, (*row_iterator).content() );
                   if(!row_iterator.horiEnd( false ))
                   {
                       row_iterator.hNext( false );
                   }
                   else
                   {
                       break;
                   }                   
               }
               // Construct the Cut
               T2 product = T2(0);
               size_t i=0;
               while(i < Inverted_Tableau.mRows.size())
               {
                   product = Scalar_Product(Inverted_Tableau,DC_Tableau,row_index,i,_lcm,diagonals,dc_positions);
                   const Variable<T1, T2>& non_basic_var = *mColumns[diagonals.at(i)].mName;
                   if(product != 0)
                   {
                       cut += non_basic_var.expression() * (product.content() * (result.mainPart().denom().content() / lcm_row.content()));
                       coefficients.push_back( product/lcm_row );
                       non_basics_proof.push_back(true);
                   }
                   else
                   {
                       non_basics_proof.push_back(false);
                   }
                   ++i;
               }
               return true; 
            }
            else
            {                
                return false;                
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
        const smtrat::Constraint* Tableau<T1,T2>::gomoryCut( const T2& _ass, size_t _rowPosition, vector<const smtrat::Constraint*>& _constrVec )
        {     
            Iterator row_iterator = Iterator( mRows.at(_rowPosition).mStartEntry, mpEntries );
            std::vector<GOMORY_SET> splitting = std::vector<GOMORY_SET>();
            // Check, whether the conditions of a Gomory Cut are satisfied
            while( !row_iterator.horiEnd( false ) )
            { 
                const Variable<T1, T2>& nonBasicVar = *mColumns[row_iterator->columnNumber()].mName;
                if( nonBasicVar.infimum() == nonBasicVar.assignment() || nonBasicVar.supremum() == nonBasicVar.assignment() )
                {
                    if( nonBasicVar.infimum() == nonBasicVar.assignment() )
                    {
                        if( (*row_iterator).content() < 0 ) splitting.push_back( J_MINUS );
                        else splitting.push_back( J_PLUS );         
                    }
                    else
                    {
                        if( (*row_iterator).content() < 0 ) splitting.push_back( K_MINUS );
                        else splitting.push_back( K_PLUS );
                    }
                }                                 
                else
                {
                    return NULL;
                }                               
                row_iterator.hNext( false );
            }
            // A Gomory Cut can be constructed              
            std::vector<T2> coeffs = std::vector<T2>();
            T2 coeff;
            T2 f_zero = _ass - T2( cln::floor1( cln::the<cln::cl_RA>( _ass.toCLN() ) ) );
            ex sum = ex();
            // Construction of the Gomory Cut 
            std::vector<GOMORY_SET>::const_iterator vec_iter = splitting.begin();
            row_iterator = Iterator( mRows.at(_rowPosition).mStartEntry, mpEntries );
            while( !row_iterator.horiEnd( false ) )
            {                 
                const Variable<T1, T2>& nonBasicVar = *mColumns[row_iterator->columnNumber()].mName;
                if( (*vec_iter) == J_MINUS )
                {
                    T2 bound = nonBasicVar.infimum().limit().mainPart();
                    coeff = -( row_iterator->content() / f_zero);
                    _constrVec.push_back( nonBasicVar.infimum().pAsConstraint() );                    
                    sum += coeff*( nonBasicVar.expression() - bound );                   
                }                 
                else if( (*vec_iter) == J_PLUS )
                {
                    T2 bound = nonBasicVar.infimum().limit().mainPart();
                    coeff = row_iterator->content()/( 1 - f_zero );
                    _constrVec.push_back( nonBasicVar.infimum().pAsConstraint() );
                    sum += coeff*( nonBasicVar.expression() - bound );                   
                }
                else if( (*vec_iter) == K_MINUS )
                {
                    T2 bound = nonBasicVar.supremum().limit().mainPart();
                    coeff = -( row_iterator->content()/( 1 - f_zero ) );
                    _constrVec.push_back( nonBasicVar.supremum().pAsConstraint() );
                    sum += coeff * ( bound - nonBasicVar.expression() );                   
                }
                else if( (*vec_iter) == K_PLUS ) 
                {
                    T2 bound = nonBasicVar.supremum().limit().mainPart();
                    coeff = (*row_iterator).content()/f_zero;
                    _constrVec.push_back( nonBasicVar.supremum().pAsConstraint() );
                    sum += coeff * ( bound - nonBasicVar.expression() );
                }     
                coeffs.push_back( coeff );
                row_iterator.hNext( false );
                ++vec_iter;
            }            
            const smtrat::Constraint* gomory_constr = smtrat::Formula::newConstraint( sum-1, smtrat::CR_GEQ, smtrat::Formula::constraintPool().realVariables() );
            ex *psum = new ex( sum - gomory_constr->constantPart() );
            Value<T1>* bound = new Value<T1>( gomory_constr->constantPart() );
            Variable<T1, T2>* var = new Variable<T1, T2>( mHeight++, true, false, psum, mDefaultBoundPosition );
            (*var).addLowerBound( bound, mDefaultBoundPosition, gomory_constr );
            typename std::vector<T2>::const_iterator coeffs_iter = coeffs.begin();
            row_iterator = Iterator( mRows.at(_rowPosition).mStartEntry, mpEntries );
            mRows.push_back( TableauHead() );
            EntryID currentStartEntryOfRow = LAST_ENTRY_ID;
            EntryID leftID;            
            while( coeffs_iter != coeffs.end() )
            {
                const Variable<T1, T2>& nonBasicVar = *mColumns[row_iterator->columnNumber()].mName;
                EntryID entryID = newTableauEntry( *coeffs_iter );
                TableauEntry<T1,T2>& entry = (*mpEntries)[entryID];
                entry.setColumnNumber( nonBasicVar.position() );
                entry.setRowNumber( mHeight - 1 );
                TableauHead& columnHead = mColumns[entry.columnNumber()];
                EntryID& columnStart = columnHead.mStartEntry;
                (*mpEntries)[columnStart].setVertNext( true, entryID );
                entry.setVertNext( false, columnStart );                
                columnStart = entryID;
                ++columnHead.mSize;
                if( currentStartEntryOfRow == LAST_ENTRY_ID )
                {
                    currentStartEntryOfRow = entryID;
                    entry.setHoriNext( true, LAST_ENTRY_ID );
                    leftID = entryID;
                }  
                else 
                {
                    (*mpEntries)[entryID].setHoriNext( true, leftID );
                    (*mpEntries)[leftID].setHoriNext( false, entryID ); 
                    leftID = entryID;
                }
                ++coeffs_iter;
                row_iterator.hNext( false );
            }            
            (*mpEntries)[leftID].setHoriNext( false, LAST_ENTRY_ID );
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
                for( auto premiseBound = learnedBound->second.premise->begin(); premiseBound != learnedBound->second.premise->end(); ++premiseBound )
                {
                    _out << _init;
                    _out << *(*premiseBound)->variable().pExpression();
                    (*premiseBound)->print( true, _out, true );
                    _out << std::endl;
                }
                _out << _init << "               | " << std::endl;
                _out << _init << "               V " << std::endl;
                _out << _init << *learnedBound->first->pExpression();
                learnedBound->second.nextWeakerBound->print( true, _out, true );
                _out << std::endl;
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                _out << _init << *learnedBound->first->pExpression();
                learnedBound->second.newBound->print( true, _out, true );
                _out << std::endl << std::endl;
                #endif
            }
            for( auto learnedBound = mLearnedUpperBounds.begin(); learnedBound != mLearnedUpperBounds.end(); ++learnedBound )
            {
                for( auto premiseBound = learnedBound->second.premise->begin(); premiseBound != learnedBound->second.premise->end(); ++premiseBound )
                {
                    _out << _init;
                    _out << *(*premiseBound)->variable().pExpression();
                    (*premiseBound)->print( true, _out, true );
                    _out << std::endl;
                }
                _out << _init << "               | " << std::endl;
                _out << _init << "               V " << std::endl;
                _out << _init << *learnedBound->first->pExpression();
                learnedBound->second.nextWeakerBound->print( true, _out, true );
                _out << std::endl;
                #ifdef LRA_INTRODUCE_NEW_CONSTRAINTS
                _out << _init << *learnedBound->first->pExpression();
                learnedBound->second.newBound->print( true, _out, true );
                _out << std::endl << std::endl;
                #endif
            }
        }
        #endif

        /**
         *
         * @param _out
         * @param _maxEntryLength
         * @param _init
         */
        template<typename T1, typename T2>
        void Tableau<T1,T2>::print( std::ostream& _out, int _maxEntryLength, const std::string _init ) const
        {
            char     frameSign     = '-';
            int width = mWidth >= (unsigned) INT_MAX ? INT_MAX - 1 : (int) mWidth; 
            _out << _init << std::setw( _maxEntryLength * (width + 1) ) << std::setfill( frameSign ) << "" << std::endl;
            _out << _init << std::setw( _maxEntryLength ) << std::setfill( ' ' ) << "#";
            for( Variable<T1,T2>* columnVar : mColumns )
            {
                std::stringstream out;
                out << *columnVar->pExpression();
                _out << std::setw( _maxEntryLength ) << out.str() + " #";
            }
            _out << std::endl;
            _out << _init << std::setw( _maxEntryLength * (width + 1) ) << std::setfill( '#' ) << "" << std::endl;
            _out << std::setfill( ' ' );
            for( Variable<T1,T2>* rowVar : mRows )
            {
                _out << _init;
                if( rowVar == NULL )
                {
                    for( size_t i = 0; i <= mWidth; ++i )
                    {
                        _out << std::setw( _maxEntryLength ) << "#";
                    }
                    _out << std::endl;
                }
                else
                {
                    std::stringstream out;
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << "(" << rowVar->factor() << ")*(";
                    #endif
                    out << *rowVar->pExpression();
                    #ifdef LRA_NO_DIVISION
                    if( !(rowVar->factor() == 1) )
                        out << ")";
                    #endif
                    _out << std::setw( _maxEntryLength ) << out.str() + " #";
                    Iterator rowIter = Iterator( rowVar->startEntry(), mpEntries );
                    size_t currentColumn = 0;
                    while( true )
                    {
                        for( size_t i = currentColumn; i < (*rowIter).columnVar()->position(); ++i )
                        {
                            _out << std::setw( _maxEntryLength ) << "0 #";
                        }
                        std::stringstream out;
                        out << (*rowIter).content();
                        _out << std::setw( _maxEntryLength ) << out.str() + " #";
                        currentColumn = (*rowIter).columnVar()->position()+1;
                        if( rowIter.hEnd( false ) )
                        {
                            for( size_t i = currentColumn; i < mWidth; ++i )
                            {
                                _out << std::setw( _maxEntryLength ) << "0 #";
                            }
                            _out << std::endl;
                            break;
                        }
                        rowIter.hMove( false );
                    }
                }
            }
            _out << _init << std::setw( _maxEntryLength * (width + 1) ) << std::setfill( frameSign ) << "" << std::endl;
            _out << std::setfill( ' ' );
        }
    }    // end namspace lra
}    // end namspace smtrat

#endif   /* LRA_TABLEAU_H */
