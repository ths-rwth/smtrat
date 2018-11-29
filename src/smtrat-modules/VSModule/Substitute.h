/**
 * Class containing a method applying a virtual substitution.
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2013-10-23
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#include "Substitution.h"
#include <bitset>

/**
 * The maximal number of splits performed, if the left-hand side of a constraints is a product of 
 * polynomials and we split the constraint into constraints over these polynomials according to the
 * relation.
 */
const unsigned MAX_PRODUCT_SPLIT_NUMBER = 64;
/**
 * The maximum number of the resulting combinations when combining according to the method combine.
 * If this number is exceeded, the method return false, and no combining is performed.
 */
const unsigned MAX_NUM_OF_COMBINATION_RESULT = 1025;

namespace smtrat {
namespace vs
{
    
    /// a vector of constraints
    typedef std::vector<smtrat::ConstraintT> ConstraintVector;
    /// a vector of vectors of constraints
    typedef std::vector<ConstraintVector> DisjunctionOfConstraintConjunctions;

    /**
     * Combines vectors.
     * @param _toCombine 	The vectors to combine.
     * @param _combination 	The resulting combination.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    template <class combineType> 
    bool combine( const std::vector< std::vector< std::vector< combineType > > >& _toCombine, std::vector< std::vector< combineType > >& _combination )
    {
        // Initialize the current combination. If there is nothing to combine or an empty vector to combine with, return the empty vector.
        if( _toCombine.empty() ) return true;
        std::vector<typename std::vector< std::vector< combineType > >::const_iterator > combination 
            = std::vector<typename std::vector< std::vector< combineType > >::const_iterator >();
        unsigned estimatedResultSize = 1;
        for( auto iter = _toCombine.begin(); iter != _toCombine.end(); ++iter )
        {
            if( iter->empty() )
                return true;
            estimatedResultSize *= (unsigned)iter->size();
            if( estimatedResultSize > MAX_NUM_OF_COMBINATION_RESULT )
                return false;
            else 
                combination.push_back( iter->begin() );
        }
        // As long as no more combination for the last vector in first vector of vectors exists.
        bool lastCombinationReached = false;
        while( !lastCombinationReached )
        {
            // Create a new combination of vectors.
            _combination.push_back( std::vector< combineType >() );
            bool previousCounterIncreased = false;
            // For each vector in the vector of vectors, choose a vector. Finally we combine
            // those vectors by merging them to a new vector and add this to the result.
            auto currentVector = _toCombine.begin();
            for( auto combineElement = combination.begin(); combineElement != combination.end(); ++combineElement )
            {
                // Add the current vectors elements to the combination.
                _combination.back().insert( _combination.back().end(), (*combineElement)->begin(), (*combineElement)->end() );
                // Set the counter.
                if( !previousCounterIncreased )
                {
                    ++(*combineElement);
                    if( *combineElement != currentVector->end() )
                        previousCounterIncreased = true;
                    else
                    {
                        if( combineElement != --combination.end() ) 
                            *combineElement = currentVector->begin();
                        else 
                            lastCombinationReached = true;
                    }
                }
                ++currentVector;
            }
        }
        return true;
    }
    
    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     * @param _toSimplify The disjunction of conjunctions to simplify.
     */
    void simplify( DisjunctionOfConstraintConjunctions& );
        
    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     * @param _toSimplify   The disjunction of conjunctions to simplify.
     * @param _conflictingVars
     * @param _solutionSpace
     */
    void simplify( DisjunctionOfConstraintConjunctions&, carl::Variables&, const smtrat::EvalDoubleIntervalMap& );
    
    /**
     * Splits all constraints in the given disjunction of conjunctions of constraints having a non-trivial 
     * factorization into a set of constraints which compare the factors instead.
     * @param _toSimplify The disjunction of conjunctions of the constraints to split.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool splitProducts( DisjunctionOfConstraintConjunctions&, bool = false );
    
    /**
     * Splits all constraints in the given conjunction of constraints having a non-trivial 
     * factorization into a set of constraints which compare the factors instead.
     * @param _toSimplify The conjunction of the constraints to split.
     * @param _result The result, being a disjunction of conjunctions of constraints.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return false, if the upper limit in the number of combinations resulting by this method is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool splitProducts( const ConstraintVector&, DisjunctionOfConstraintConjunctions&, bool = false );
    
    /**
     * Splits the given constraint into a set of constraints which compare the factors of the
     * factorization of the constraints considered polynomial.
     * @param _constraint A pointer to the constraint to split.
     * @param _onlyNeq A flag indicating that only constraints with the relation symbol != are split.
     * @return The resulting disjunction of conjunctions of constraints, which is semantically equivalent to
     *          the given constraint.
     */
    DisjunctionOfConstraintConjunctions splitProducts( const smtrat::ConstraintT&, bool = false );
    
    void splitSosDecompositions( DisjunctionOfConstraintConjunctions& );
    
    /**
     * For a given constraint f_1*...*f_n ~ 0 this method computes all combinations of constraints
     * f_1 ~_1 0 ... f_n ~_n 0 such that 
     * 
     *          f_1 ~_1 0 and ... and f_n ~_n 0   iff   f_1*...*f_n ~ 0 
     * holds.
     * @param _constraint A pointer to the constraint to split this way.
     * @return The resulting combinations.
     */
    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::ConstraintT& );
    
    /**
     * @param _length The maximal length of the bit strings with odd parity to compute.
     * @param _strings All bit strings of length less or equal the given length with odd parity.
     */
    void getOddBitStrings( size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings );
        
    /**
     * @param _length The maximal length of the bit strings with even parity to compute.
     * @param _strings All bit strings of length less or equal the given length with even parity.
     */
    void getEvenBitStrings( size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings );
    
    /**
     * Prints the given disjunction of conjunction of constraints.
     * @param _substitutionResults The disjunction of conjunction of constraints to print.
     */
    void print( DisjunctionOfConstraintConjunctions& _substitutionResults );
    
    /**
     * Applies a substitution to a constraint and stores the results in the given vector.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution.
     * @return false, if the upper limit in the number of combinations in the result of the substitution is exceeded.
     *                 Note, that this hinders a combinatorial blow up.
     *          true, otherwise.
     */
    bool substitute( const smtrat::ConstraintT&, const Substitution&, DisjunctionOfConstraintConjunctions&, bool _accordingPaper, carl::Variables&, const smtrat::EvalDoubleIntervalMap& );
    
    /**
     * Applies a substitution of a variable to a term, which is not minus infinity nor a to an square root expression plus an infinitesimal.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    bool substituteNormal( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper, carl::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    bool substituteNormalSqrtEq( const smtrat::Poly& _radicand, const smtrat::Poly& _q, const smtrat::Poly& _r, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "!=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    -----------------------
     *                                      _s
     *
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    bool substituteNormalSqrtNeq( const smtrat::Poly& _radicand, const smtrat::Poly& _q, const smtrat::Poly& _r, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is less.
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ----------------------
     *                                      _s
     *
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _s The denominator of the expression containing the square root.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    bool substituteNormalSqrtLess( const smtrat::Poly& _radicand, const smtrat::Poly& _q, const smtrat::Poly& _r, const smtrat::Poly& _s, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is less or equal.
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ----------------------
     *                                      _s
     *
     * @param _radicand The radicand of the square root.
     * @param _q The summand not containing the square root.
     * @param _r The coefficient of the radicand.
     * @param _s The denominator of the expression containing the square root.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     */
    bool substituteNormalSqrtLeq( const smtrat::Poly& _radicand, const smtrat::Poly& _q, const smtrat::Poly& _r, const smtrat::Poly& _s, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    bool substitutePlusEps( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, bool _accordingPaper, carl::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Sub-method of substituteEps, where one of the gradients in the
     * point represented by the substitution must be negative if the given relation is less
     * or positive if the given relation is greater. 
     * @param _cons The constraint to substitute in.
     * @param _subs The substitution to apply.
     * @param _relation The relation symbol, deciding whether the substitution result must be negative or positive.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _accordingPaper A flag that indicates whether to apply the virtual substitution rules according to the paper "Quantifier elimination
     *                        for real algebra - the quadratic case and beyond." by Volker Weispfenning (true) or in an adapted way which omits a higher
     *                        degree in the result by splitting the result in more cases (false).
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    bool substituteEpsGradients( const smtrat::ConstraintT& _cons, const Substitution& _subs, const carl::Relation _relation, DisjunctionOfConstraintConjunctions&, bool _accordingPaper, carl::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     * @param _conflictingVariables If a conflict with the given solution space occurs, the variables being part of this conflict are stored in this
     *                               container.
     * @param _solutionSpace The solution space in form of double intervals of the variables occurring in the given constraint.
     */
    void substituteInf( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, carl::Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace );
    
    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is less or greater.
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteInfLessGreater( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result );
    
    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     * The constraints left hand side then should look like:   ax^2+bx+c
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteTrivialCase( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result );
    
    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     * The constraints left hand side then should looks like:   ax^2+bx+c
     * @param _cons   The constraint to substitute in.
     * @param _subs   The substitution to apply.
     * @param _result The vector, in which to store the results of this substitution. It is semantically a disjunction of conjunctions of constraints.
     */
    void substituteNotTrivialCase( const smtrat::ConstraintT&, const Substitution&, DisjunctionOfConstraintConjunctions& );
    
}    // end namspace vs
}
