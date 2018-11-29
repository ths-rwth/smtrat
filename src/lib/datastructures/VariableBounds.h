/**
 * @file VariableBounds.h
 * @author Florian Corzilius
 * @since 2012-10-04
 * @version 2013-02-05
 */

#pragma once

#include <smtrat-common/model.h>
#include <iomanip>

namespace smtrat
{
    namespace vb
    {
        // Forward declaration
        template <typename T> class Variable;

        /**
         * Class for the bound of a variable.
         */
        template <typename T> class Bound
        {
            public:
                /// The type of a bounds.
                enum Type { STRICT_LOWER_BOUND = 0, WEAK_LOWER_BOUND = 1, EQUAL_BOUND = 2, WEAK_UPPER_BOUND = 3, STRICT_UPPER_BOUND = 4 };

            private:
                /// The type of this bound.
                Type mType;
                /// A pointer to bound value, which is plus or minus infinity if the pointer is NULL.
                Rational* mpLimit;
                /// The variable for which the bound is declared.
                Variable<T>* const mpVariable;
                /// A set of origins of the bound, e.g., x-3<0 is the origin of the bound <3.
                std::set<T,carl::less<T,false>>* const mpOrigins; // Here, we cannot use the carl::PointerSet, which falls back on the comparison operator
                                                     // of T, as we must ensure to store for every pointer to T one origin.
                
            public:
                
                /**
                 * Constructs this bound.
                 * @param _limit A pointer to the limit (rational) of the bound. It is NULL, if the limit is not finite.
                 * @param _variable The variable to which this bound belongs.
                 * @param _type The type of the bound (either it is an equal bound or it is weak resp. strict and upper resp. lower)
                 */
                Bound( Rational* const _limit, Variable<T>* const _variable, Type _type );

                /**
                 * Destructs this bound.
                 */
                ~Bound();
                
                /**
                 * Checks whether the this bound is smaller than the given one.
                 * @param _bound The bound to compare with.
                 * @return true,    if for this bound (A) and the given bound (B) it holds that:
                 *                      A is not inf   and   B is inf,
                 *                      A smaller than B, where A and B are rationals,
                 *                      A equals B, where A and B are rationals, but A is an equal bound but B is not;
                 *          false,   otherwise.
                 */
                bool operator<( const Bound<T>& _bound ) const;
                
                /**
                 * Prints the bound on the given output stream.
                 * @param _out The output stream to print on.
                 * @param _bound The bound to print.
                 * @return The output stream after printing the bound on it.
                 */
                template <typename T1> friend std::ostream& operator<<( std::ostream& _out, const Bound<T1>& _bound );
                
                /**
                 * Prints this bound on the given stream.
                 * @param _out The stream to print on.
                 * @param _withRelation A flag indicating whether to print also a relation symbol in front of the bound value.
                 */
                void print( std::ostream& _out, bool _withRelation = false ) const;


                /**
                 * @return A constant reference to the value of the limit. Note, that it must be ensured that
                 *          the bound is finite before calling this method.
                 */
                const Rational& limit() const
                {
                    return *mpLimit;
                }

                /**
                 * @return A pointer to the limit of this bound.
                 */
                const Rational* pLimit() const
                {
                    return mpLimit;
                }

                /**
                 * @return true, if the bound infinite;
                 *          false, otherwise.
                 */
                bool isInfinite() const
                {
                    return mpLimit == NULL;
                }

                /**
                 * @return The type of this bound.
                 */
                Type type() const
                {
                    return mType;
                }

                /**
                 * @return true, if the bound is an upper bound;
                 *          false, otherwise.
                 */
                bool isUpperBound() const
                {
                    return mType > WEAK_LOWER_BOUND;
                }
                
                /**
                 * @return true, if the bound is a lower bound;
                 *          false, otherwise.
                 */
                bool isLowerBound() const
                {
                    return mType < WEAK_UPPER_BOUND;
                }

                /**
                 * @return A pointer to the variable wrapper considered by this bound.
                 */
                Variable<T>* pVariable() const
                {
                    return mpVariable;
                }

                /**
                 * @return A constant reference to the variable wrapper considered by this bound.
                 */
                const Variable<T>& variable() const
                {
                    return *mpVariable;
                }

                /**
                 * @return true, if this bound is active, which means that there is at least one origin for it left.
                 *                Note, that origins can be removed belatedly.
                 *          false, otherwise.
                 */
                bool isActive() const
                {
                    return !mpOrigins->empty();
                }

                /**
                 * Adds an origin to this bound.
                 * @param _origin The origin to add.
                 * @return true, if this has activated this bound;
                 *          false, if the bound was already active before.
                 */
                bool activate( const T& _origin ) const
                {
                    assert(mpOrigins->find(_origin) == mpOrigins->end());
                    mpOrigins->insert( _origin );
                    return mpOrigins->size() == 1;
                }
                
                /**
                 * Removes an origin from this bound.
                 * @param _origin The origin to add.
                 * @return true, if this has deactivated this bound;
                 *          false, if the bound was already inactive before.
                 */
                bool deactivate( const T& _origin ) const
                {
                    assert( mpOrigins->find( _origin ) != mpOrigins->end() );
                    mpOrigins->erase( _origin );
                    return mpOrigins->empty();
                }

                /**
                 * @return A constant reference to the set of origins of this bound.
                 */
                const std::set<T,carl::less<T,false>>& origins() const
                {
                    return *mpOrigins;
                }
        };

        /**
         * Class for a variable.
         */
        template <typename T> class Variable
        {
            /**
             * Compares two pointers showing to bounds.
             */
            struct boundPointerComp
            {
                /**
                 * @param pBoundA A pointer to a bound.
                 * @param pBoundB A pointer to a bound.
                 * @return true, if the bound, the first pointer shows to is less than the bound the second pointer shows to.
                 */
                bool operator ()( const Bound<T>* const pBoundA, const Bound<T>* const pBoundB ) const
                {
                    return (*pBoundA) < (*pBoundB);
                }
            };

            /// A set of bounds.
            typedef std::set<const Bound<T>*, boundPointerComp> BoundSet;
            
            private:
                /// A flag that indicates that the stored exact interval of this variable is up to date.
                mutable bool    mUpdatedExactInterval;
                /// A flag that indicates that the stored double interval of this variable is up to date.
                mutable bool    mUpdatedDoubleInterval;
                /// The least upper bound of this variable.
                const Bound<T>* mpSupremum;
                /// The greatest lower bound of this variable.
                const Bound<T>* mpInfimum;
                /// The set of all upper bounds of this variable.
                BoundSet        mUpperbounds;
                /// The set of all lower bounds of this variable.
                BoundSet        mLowerbounds;

            public:
                /**
                 * Constructs this variable.
                 */
                Variable();

                /*
                 * Destructs this variable.
                 */
                ~Variable();

                /**
                 * @return true, if there is a conflict;
                 *          false, otherwise.
                 */
                bool conflicting() const;
                
                /**
                 * Adds the bound corresponding to the constraint to the given variable. The constraint
                 * is expected to contain only one variable and this one only linearly.
                 * @param _constraint A pointer to a constraint of the form ax~b.
                 * @param _var Hence, the variable x.
                 * @param _origin The origin of the constraint. This is could be the constraint itself or anything else 
                 *                 in the data structure which uses this object.
                 * @param _limit
                 * @return The added bound.
                 */
                const Bound<T>* addBound( const ConstraintT& _constraint, const carl::Variable& _var, const T& _origin );
                
                /**
                 * Updates the infimum and supremum of this variable.
                 * @param _changedBound The bound, for which we certainly know that it got deactivated before.
                 * @return true, if there is a conflict;
                 *          false, otherwise.
                 */
                bool updateBounds( const Bound<T>& _changedBound );

                /**
                 * @return true, if the stored exact interval representing the variable's bounds is up to date.
                 *          false, otherwise
                 */
                bool updatedExactInterval() const
                {
                    return mUpdatedExactInterval;
                }

                /**
                 * Sets the flag indicating that the stored exact interval representing the variable's bounds is up to date to false.
                 */
                void exactIntervalHasBeenUpdated() const
                {
                    mUpdatedExactInterval = false;
                }
                
                /**
                 * @return true, if the stored double interval representing the variable's bounds is up to date.
                 *          false, otherwise
                 */
                bool updatedDoubleInterval() const
                {
                    return mUpdatedDoubleInterval;
                }
                
                /**
                 * Sets the flag indicating that the stored double interval representing the variable's bounds is up to date to false.
                 */
                void doubleIntervalHasBeenUpdated() const
                {
                    mUpdatedDoubleInterval = false;
                }

                /**
                 * @return A pointer to the supremum of this variable.
                 */
                const Bound<T>* pSupremum() const
                {
                    return mpSupremum;
                }

                /**
                 * @return A constant reference to the supremum of this variable.
                 */
                const Bound<T>& supremum() const
                {
                    return *mpSupremum;
                }

                /**
                 * @return A pointer to the infimum of this variable.
                 */
                const Bound<T>* pInfimum() const
                {
                    return mpInfimum;
                }

                /**
                 * @return A constant reference to the infimum of this variable.
                 */
                const Bound<T>& infimum() const
                {
                    return *mpInfimum;
                }

                /**
                 * @return A constant reference to the set of upper bounds of this variable.
                 */
                const BoundSet& upperbounds() const
                {
                    return mUpperbounds;
                }
                
                /**
                 * @return A constant reference to the set of lower bounds of this variable.
                 */
                const BoundSet& lowerbounds() const
                {
                    return mLowerbounds;
                }
        };

        /**
         * Class to manage the bounds of a variable.
         */
        template <typename T> class VariableBounds
        {
            public:
                /// A map from Constraint pointers to Bound pointers.
                typedef std::map<ConstraintT,const Bound<T>*> ConstraintBoundMap;
                /// A hash-map from arithmetic variables to variables managing the bounds.
                typedef carl::FastMap<carl::Variable, Variable<T>*>  VariableMap;
            private:
                /// A pointer to one of the conflicting variables (its supremum is smaller than its infimum)
                /// or NULL if there is no conflict.
                Variable<T>*          mpConflictingVariable;
                /// A mapping from arithmetic variables to the variable objects storing the bounds.
                VariableMap*          mpVariableMap;
                /// A mapping from constraint pointer to the corresponding bounds.
                ConstraintBoundMap*   mpConstraintBoundMap;
                /// The stored exact interval map representing the currently tightest bounds.
                /// Note, that it is updated on demand.
                mutable EvalRationalIntervalMap       mEvalIntervalMap;
                /// The stored double interval map representing the currently tightest bounds.
                /// Note, that it is updated on demand.
                mutable EvalDoubleIntervalMap mDoubleIntervalMap;
                /// Stores the constraints which cannot be used to infer a bound for a variable.
                ConstraintsT mNonBoundConstraints;
                /// Stores deductions which this variable bounds manager has detected.
                mutable std::unordered_set<std::vector<ConstraintT>> mBoundDeductions;
            public:
                /**
                 * Constructs a variable bounds manager.
                 */
                VariableBounds();

                /**
                 * Destructs a variable bounds manager.
                 */
                ~VariableBounds();
                void clear();
                
                bool empty() const
                {
                    return mpConstraintBoundMap->empty();
                }
                
                /**
                 * Updates the variable bounds by the given constraint.
                 * @param _constraint The constraint to consider.
                 * @param _origin The origin of the given constraint.
                 * @return true, if the variable bounds have been changed;
                 *          false, otherwise.
                 */
                bool addBound( const ConstraintT& _constraint, const T& _origin );
				
				bool addBound( const FormulaT& _formula, const T& _origin );
                
                /**
                 * Removes all effects the given constraint has on the variable bounds.
                 * @param _constraint The constraint, which effects shall be undone for the variable bounds.
                 * @param _origin The origin of the given constraint.
                 * @return 2, if the variables supremum or infimum have been changed;
                 *          1, if the constraint was a (not the strictest) bound;
                 *          0, otherwise.
                 */
                unsigned removeBound( const ConstraintT& _constraint, const T& _origin );
				
				unsigned removeBound( const FormulaT& _formula, const T& _origin );
                
                /**
                 * Removes all effects the given constraint has on the variable bounds.
                 * @param _constraint The constraint, which effects shall be undone for the variable bounds.
                 * @param _origin The origin of the given constraint.
                 * @param _changedVariable The variable whose interval domain has been changed, if the return value is 2.
                 * @return 2, if the variables supremum or infimum have been changed;
                 *          1, if the constraint was a (not the strictest) bound;
                 *          0, otherwise.
                 */
                unsigned removeBound( const ConstraintT& _constraint, const T& _origin, carl::Variable*& _changedVariable );
                
                /**
                 * Creates an evalintervalmap corresponding to the variable bounds.
                 * @return The variable bounds as an evalintervalmap.
                 */
                const EvalRationalIntervalMap& getEvalIntervalMap() const;
                
                /**
                 * Creates an interval corresponding to the variable bounds of the given variable.
                 * @param _var The variable to compute the variable bounds as interval for.
                 * @return The variable bounds as an interval.
                 */
                const RationalInterval& getInterval( const carl::Variable& _var ) const;
				
				/**
                 * Creates an interval corresponding to the bounds of the given monomial.
                 * @param _mon The monomial to compute the bounds as interval for.
                 * @return The monomial bounds as an interval.
                 */
				RationalInterval getInterval( carl::Monomial::Arg _mon ) const;
				
				/**
                 * Creates an interval corresponding to the bounds of the given term.
                 * @param _term The term to compute the bounds as interval for.
                 * @return The term bounds as an interval.
                 */
				RationalInterval getInterval( const TermT& _term ) const;
                
                /**
                 * Creates an interval map corresponding to the variable bounds.
                 * @return The variable bounds as an interval map.
                 */
                const smtrat::EvalDoubleIntervalMap& getIntervalMap() const;
                
                /**
                 * Creates a double interval corresponding to the variable bounds of the given variable.
                 * @param _var The variable to compute the variable bounds as double interval for.
                 * @return The variable bounds as a double interval.
                 */
                const carl::Interval<double>& getDoubleInterval( const carl::Variable& _var ) const;
                
                /**
                 * @param _var The variable to get origins of the bounds for.
                 * @return The origin constraints of the supremum and infimum of the given variable.
                 */
                std::vector<T> getOriginsOfBounds( const carl::Variable& _var ) const;
                std::set<T> getOriginSetOfBounds( const carl::Variable& _var ) const;
                
                /**
                 * @param _variables The variables to get origins of the bounds for.
                 * @return The origin constraints of the supremum and infimum of the given variables.
                 */
                std::vector<T> getOriginsOfBounds( const carl::Variables& _variables ) const;
                std::set<T> getOriginSetOfBounds( const carl::Variables& _variables ) const;
                
                /**
                 * Collect the origins to the supremums and infimums of all variables.
                 * @return A set of origins corresponding to the supremums and infimums of all variables.
                 */
                std::vector<T> getOriginsOfBounds() const;
                std::set<T> getOriginSetOfBounds() const;
                
                /**
                 * @return The deductions which this variable bounds manager has detected.
                 */
                std::vector<std::pair<std::vector<ConstraintT>, ConstraintT>> getBoundDeductions() const;
                
                /**
                 * Prints the variable bounds.
                 * @param _out The output stream to print on.
                 * @param _init A string which is displayed at the beginning of every row.
                 * @param _printAllBounds A flag that indicates whether to print also the bounds of each variable (=true).
                 */
                void print( std::ostream& _out = std::cout, const std::string _init = "", bool _printAllBounds = false ) const;

                /**
                 * @return true, if there is a conflicting variable;
                 *          false, otherwise.
                 */
                bool isConflicting() const
                {
                    return mpConflictingVariable != NULL;
                }

                /**
                 * @return The origins which cause the conflict. This method can only be called, if there is a conflict.
                 */
                std::set<T> getConflict() const
                {
                    assert( isConflicting() );
                    assert( !mpConflictingVariable->infimum().isInfinite() && !mpConflictingVariable->supremum().isInfinite() );
                    std::set<T> conflict;
                    conflict.insert( *mpConflictingVariable->infimum().origins().begin() );
                    conflict.insert( *mpConflictingVariable->supremum().origins().begin() );
                    return conflict;
                }
        };
        
        /**
         * Prints the contents of the given variable bounds manager to the given stream.
         * @param _os The stream to print on.
         * @param _vs The variable bounds manager to print. 
         * @return The stream after printing on it.
         */
        template<typename Type>
        inline std::ostream& operator<<( std::ostream& _os, const VariableBounds<Type>& _vs )
        {
            _vs.print(_os);
            return _os;
        }
    }   // namespace vb
}    // namespace smtrat

#include "VariableBounds.tpp"
