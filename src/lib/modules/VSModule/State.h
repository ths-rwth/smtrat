/* SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
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
 * Class to create a decision tuple object.
 * @author Florian Corzilius
 * @since 2010-05-11
 * @version 2011-12-05
 */

#ifndef SMTRAT_VS_STATE_H
#define SMTRAT_VS_STATE_H

#include <map>
#include <limits.h>
#include <ginacra/ginacra.h>
#include "Substitution.h"
#include "../../misc/VS_Tools.hpp"
#include "config.h"
#ifdef SMTRAT_VS_VARIABLEBOUNDS
#include "../../VariableBounds.h"
#define SMTRAT_VS_VARIABLEBOUNDS_B
#endif

namespace vs
{
    template <class elementType> struct setOfPointerComp
    {
        bool operator() ( const std::set< elementType > set1, const std::set< elementType > set2 )
        {
            class std::set< elementType >::const_iterator elem1 = set1.begin();
            class std::set< elementType >::const_iterator elem2 = set2.begin();
            while( elem1!=set1.end() && elem2!=set2.end() )
            {
                if( set1.key_comp()( *elem2, *elem1 ) )
                    return false;
                else if( set1.key_comp()( *elem1, *elem2 ) )
                    return true;
                else
                {
                    elem1++;
                    elem2++;
                }
            }
            if( elem2!=set2.end() )
                return true;
            else
                return false;
        }
    };

    struct setOfCondPointerComp
    {
        bool operator() ( const ConditionSet set1, const ConditionSet set2 )
        {
            ConditionSet::const_iterator cond1 = set1.begin();
            ConditionSet::const_iterator cond2 = set2.begin();
            while( cond1!=set1.end() && cond2!=set2.end() )
            {
                if( set1.key_comp()( *cond2, *cond1 ) )
                    return false;
                else if( set1.key_comp()( *cond1, *cond2 ) )
                    return true;
                else
                {
                    cond1++;
                    cond2++;
                }
            }
            if( cond2!=set2.end() )
                return true;
            else
                return false;
        }
    };

    typedef std::set< ConditionSet, setOfCondPointerComp >	ConditionSetSet	;

    struct setOfSetsOfCondPointerComp
    {
        bool operator() ( const ConditionSetSet setOfSet1, const ConditionSetSet setOfSet2 )
        {
            ConditionSetSet::const_iterator set1 = setOfSet1.begin();
            ConditionSetSet::const_iterator set2 = setOfSet2.begin();
            while( set1!=setOfSet1.end() && set2!=setOfSet2.end() )
            {
                if( setOfSet1.key_comp()( *set2, *set1 ) )
                    return false;
                else if( setOfSet1.key_comp()( *set1, *set2 ) )
                    return true;
                else
                {
                    set1++;
                    set2++;
                }
            }
            if( set2!=setOfSet2.end() )
                return true;
            else
                return false;
        }
    };

    typedef std::set< ConditionSetSet, setOfSetsOfCondPointerComp > ConditionSetSetSet;

    struct unsignedGreater
    {
        bool operator() ( const unsigned& lhs, const unsigned& rhs ) const
        {
            return lhs>rhs;
        }
    };

    struct unsignedSmaller
    {
        bool operator() ( const unsigned& lhs, const unsigned& rhs ) const
        {
            return lhs<rhs;
        }
    };

    struct subComp
    {
        bool operator() ( const Substitution* const pSubA, const Substitution* const pSubB ) const
        {
            if( pSubA==NULL && pSubB==NULL )
                return false;
            else if( pSubA==NULL )
                return true;
            else if( pSubB==NULL )
                return false;
            else
                return (*pSubA)<(*pSubB);
        }
    };
    
    class State;

    typedef std::list< const Condition* >            ConditionList;
    typedef std::vector< ConditionList >             DisjunctionOfConditionConjunctions;
    typedef std::vector< const smtrat::Constraint* > TS_ConstraintConjunction;
    typedef std::list< State* >						 StateVector;

    class State
    {
    public:
        // A unsigned integer is between 0 and 4.294.967.295, so there are 4.294 different valuations.
        // The remaining 6 digits are to make a valuation unique, so there are 967.295 different IDs.
        static const unsigned VALUATION_FACTOR			 = 1000000;
        static const unsigned MAX_CONSTRAINT_VALUATION 	 = 10;
        static const unsigned MIN_VALUATION				 = 0;
        static const unsigned MAX_VALUATION				 = UINT_MAX;
        static const unsigned MAX_ID	  	        	 = UINT_MAX;
        static const signed   MAX_SOLVABLE_DEGREE 		 = 2;
        static const unsigned MAXIMUM_VARIABLE_VALUATION = 10000000;
        
        // Intern type structure.
        enum Type{ TEST_CANDIDATE_TO_GENERATE, SUBSTITUTION_TO_APPLY, COMBINE_SUBRESULTS };
        
        typedef std::map< const Substitution* const, ConditionSetSetSet, subComp > ConflictSets;
        typedef std::vector< std::pair< ConditionList, bool > > 				   SubstitutionResult;
        typedef std::vector< SubstitutionResult > 								   SubstitutionResults;
        typedef std::vector< std::pair< unsigned, unsigned > >                     SubResultCombination;
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        typedef smtrat::vb::VariableBounds< Condition >                            VariableBounds;
        #endif
    private:

        // Members.
        bool				  mConditionsSimplified;
        bool				  mHasChildrenToInsert;
        bool				  mHasRecentlyAddedConditions;
        bool				  mInconsistent;
        bool				  mMarkedAsDeleted;
        bool				  mSubResultsSimplified;
        bool				  mTakeSubResultCombAgain;
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        bool                  mTestCandidateCheckedForBounds;
        bool                  mTestCandidateInBoundsCreated;
        #endif
        bool				  mToHighDegree;
        bool				  mTryToRefreshIndex;
        unsigned		      mID;
        unsigned		      mValuation;
        Type                  mType;
        std::string*		  mpIndex;
        const Condition*      mpOriginalCondition;
        State*				  mpFather;
        Substitution*		  mpSubstitution;
        SubstitutionResults*  mpSubstitutionResults;
        SubResultCombination* mpSubResultCombination;
        ConditionList*        mpConditions;
        ConflictSets*		  mpConflictSets;
        StateVector* 		  mpChildren;
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        VariableBounds*       mpVariableBounds;
        #endif
    public:

        // Constructors.
        State();
        State( State* const, const Substitution& );

        // Destructor.
        ~State();

        // Methods.
        bool isRoot() const
        {
            return mpFather == NULL;
        }

        bool toHighDegree() const
        {
            return mToHighDegree;
        }

        bool& rToHighDegree()
        {
            return mToHighDegree;
        }

        #ifndef VS_USE_REDLOG
        bool markedAsDeleted() const
        {
            return mMarkedAsDeleted;
        }

        bool& rMarkedAsDeleted()
        {
            return mMarkedAsDeleted;
        }
        #endif

        bool hasChildrenToInsert() const
        {
            return mHasChildrenToInsert;
        }

        bool& rHasChildrenToInsert()
        {
            return mHasChildrenToInsert;
        }

        const std::string& index() const
        {
            return *mpIndex;
        }

        unsigned& rValuation()
        {
            return mValuation;
        }

        unsigned valuation() const
        {
            return mValuation;
        }

        unsigned id() const
        {
            return mID;
        }

        StateVector& rChildren()
        {
            return *mpChildren;
        }

        const StateVector& children() const
        {
            return *mpChildren;
        }

        State* const pFather() const
        {
            return mpFather;
        }

        const State& father() const
        {
            return *mpFather;
        }

        State& rFather()
        {
            return *mpFather;
        }

        ConflictSets& rConflictSets()
        {
            return *mpConflictSets;
        }

        const ConflictSets&	conflictSets() const
        {
            return *mpConflictSets;
        }

        bool& rHasRecentlyAddedConditions()
        {
            return mHasRecentlyAddedConditions;
        }

        bool hasRecentlyAddedConditions() const
        {
            return mHasRecentlyAddedConditions;
        }

        bool& rInconsistent()
        {
            return mInconsistent;
        }

        bool isInconsistent() const
        {
            return mInconsistent;
        }

        ConditionList& rConditions()
        {
            return *mpConditions;
        }

        const ConditionList& conditions() const
        {
            return *mpConditions;
        }

        Substitution& rSubstitution()
        {
            return *mpSubstitution;
        }

        const Substitution&	substitution() const
        {
            return *mpSubstitution;
        }

        SubstitutionResults& rSubstitutionResults()
        {
            return *mpSubstitutionResults;
        }

        const SubstitutionResults& substitutionResults() const
        {
            return *mpSubstitutionResults;
        }

        SubResultCombination& rSubResultCombination()
        {
            return *mpSubResultCombination;
        }

        const SubResultCombination&	subResultCombination() const
        {
            return *mpSubResultCombination;
        }

        const Substitution* const pSubstitution() const
        {
            return mpSubstitution;
        }

        bool conditionsSimplified() const
        {
            return mConditionsSimplified;
        }

        bool subResultsSimplified() const
        {
            return mSubResultsSimplified;
        }

        bool& rSubResultsSimplified()
        {
            return mSubResultsSimplified;
        }

        bool takeSubResultCombAgain() const
        {
            return mTakeSubResultCombAgain;
        }

        bool& rTakeSubResultCombAgain()
        {
            return mTakeSubResultCombAgain;
        }

        bool tryToRefreshIndex() const
        {
            return mTryToRefreshIndex;
        }

        bool hasSubResultsCombination() const
        {
            return (mpSubResultCombination!=NULL && !mpSubResultCombination->empty());
        }

        bool hasSubstitutionResults() const
        {
            return mpSubstitutionResults!=NULL;
        }

        bool unfinished() const
        {
            return (mpSubstitutionResults->size()>mpSubResultCombination->size());
        }

        const Type type() const
        {
            return mType;
        }

        Type& rType()
        {
            return mType;
        }

        const Condition* pOriginalCondition() const
        {
            return mpOriginalCondition;
        }

        const Condition& originalCondition() const
        {
            return *mpOriginalCondition;
        }

        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        const VariableBounds& variableBounds() const
        {
            return *mpVariableBounds;
        }

        VariableBounds& rVariableBounds()
        {
            return *mpVariableBounds;
        }
        #endif

        void setOriginalCondition( const Condition* const _pOCondition )
        {
            mpOriginalCondition=_pOCondition;
        }

        // Data read only methods.
        unsigned treeDepth() const;
        bool substitutionApplicable() const;
        bool substitutionApplicable( const smtrat::Constraint& ) const;
        bool hasNoninvolvedCondition() const;
        bool hasChildWithID() const;
        bool occursInEquation( const std::string& ) const;
        bool hasFurtherUncheckedTestCandidates() const;
        void variables( std::set< std::string >& ) const;
        unsigned numberOfNodes() const;
        const std::pair< unsigned, unsigned > valuationPlusID() const;
        bool checkSubResultsCombs() const;

        // Data read and write methods.
        State& root();
        bool unfinishedAncestor( State*& );
        bool bestCondition( const Condition*&, unsigned );
        ConditionList::iterator	constraintExists( const smtrat::Constraint& );

        // Manipulating methods.
        void simplify();
        bool simplify( ConditionList&, ConditionSetSet&, bool = false );
        void setIndex( const std::string& );
        bool setID( const unsigned );
        void addConflictSet( const Substitution* const, ConditionSetSet& );
        void addConflicts( const Substitution* const, ConditionSetSet& );
        void resetConflictSets();
        bool updateOCondsOfSubstitutions( const Substitution& );
        void addSubstitutionResults( std::vector< DisjunctionOfConditionConjunctions >& );
        bool extendSubResultCombination();
        bool nextSubResultCombination();
        const ConditionList getCurrentSubresultCombination() const;
        bool refreshConditions();
        void initConditionFlags();
        bool initIndex( const GiNaC::symtab& );
        void addCondition( const smtrat::Constraint*, const ConditionSet&, const unsigned, const bool );
        bool checkConditions();
        int deleteOrigins( std::set<const Condition*>& );
        void deleteOriginsFromChildren( std::set<const Condition*>& );
        void deleteOriginsFromConflictSets( std::set<const Condition*>&, bool );
        void deleteOriginsFromSubstitutionResults( std::set<const Condition*>& );
        void deleteConditions( std::set<const Condition*>& );
        int addChild( const std::string&, const GiNaC::ex&, const Substitution_Type&, const ConditionSet& );
        int addChild( const GiNaC::ex&, const smtrat::Constraint_Relation&, const std::string&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const Substitution_Type&, const GiNaC::symtab&, const ConditionSet& );
        int addChild( const GiNaC::ex&, const smtrat::Constraint_Relation&, const GiNaC::ex&, const smtrat::Constraint_Relation&, const std::string&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const GiNaC::ex&, const Substitution_Type&, const GiNaC::symtab&, const ConditionSet& );
        void updateValuation();
        void passConflictToFather( bool = false );
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        bool checkTestCandidatesForBounds();
        std::vector< GiNaCRA::DoubleInterval > solutionSpace( ConditionSet& );
        bool hasRootsInVariableBounds( const Condition* );
        #endif

        // Printing methods.
        void print( const std::string = "***", std::ostream& = std::cout ) const;
        void printAlone( const std::string = "***", std::ostream& = std::cout ) const;
        void printConditions( const std::string = "***", std::ostream& = std::cout, bool = false ) const;
        void printSubstitutionResults( const std::string = "***", std::ostream&	= std::cout	) const;
        void printSubstitutionResultCombination( const std::string = "***", std::ostream& = std::cout	) const;
        void printSubstitutionResultCombinationAsNumbers( const std::string = "***", std::ostream& = std::cout ) const;
        void printConflictSets( const std::string = "***", std::ostream& = std::cout ) const;

        // Static methods.
        static unsigned coveringSet( const ConditionSetSetSet&, ConditionSet&, const unsigned );
        static signed compareConstraints( const smtrat::Constraint&, const smtrat::Constraint& );
    };
} // end namspace vs
#endif