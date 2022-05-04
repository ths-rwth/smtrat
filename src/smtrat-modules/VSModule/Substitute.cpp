/**
 * Class containing a method applying a virtual substitution.
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2013-10-23
 */

#include "Substitute.h"
#include <cmath>
#include <limits>

#include <carl/core/polynomialfunctions/Derivative.h>
#include <carl/core/polynomialfunctions/SoSDecomposition.h>
#include <carl/constraint/IntervalEvaluation.h>
#include <carl/vs/Substitution.h>

//#define VS_DEBUG_SUBSTITUTION
const unsigned MAX_NUM_OF_TERMS = 512;

using namespace carl;

namespace smtrat {
namespace vs
{
    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
        bool containsEmptyDisjunction = false;
        auto conj = _toSimplify.begin();
        while( conj != _toSimplify.end() )
        {
            bool conjInconsistent = false;
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( *cons == smtrat::ConstraintT( false ) )
                {
                    conjInconsistent = true;
                    break;
                }
                else if( *cons == smtrat::ConstraintT( true ) )
                    cons = (*conj).erase( cons );
                else
                    cons++;
            }
            bool conjEmpty = (*conj).empty();
            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
            {
                // Delete the conjunction.
                conj->clear();
                conj = _toSimplify.erase( conj );
            }
            else
                conj++;
            if( !containsEmptyDisjunction && conjEmpty )
                containsEmptyDisjunction = true;
        }
    }

    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify, Variables& _conflictingVars, const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        bool containsEmptyDisjunction = false;
        auto conj = _toSimplify.begin();
        while( conj != _toSimplify.end() )
        {
            bool conjInconsistent = false;
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( *cons == smtrat::ConstraintT( false ) )
                {
                    conjInconsistent = true;
                    break;
                }
                else if( *cons == smtrat::ConstraintT( true ) )
                    cons = (*conj).erase( cons );
                else
                {
                    unsigned conflictingWithSolutionSpace = consistentWith(cons->constr(), _solutionSpace );
                    
//                    std::cout << "Is  " << cons << std::endl;
//                    std::cout << std::endl;
//                    std::cout << "consistent with  " << std::endl;
//                    for( auto iter = _solutionSpace.begin(); iter != _solutionSpace.end(); ++iter )
//                        std::cout << iter->first << " in " << iter->second << std::endl;
//                    std::cout << "   ->  " << conflictingWithSolutionSpace << std::endl;
                    
                    if( conflictingWithSolutionSpace == 0 )
                    {
                        auto vars = carl::variables(*cons);
                        _conflictingVars.insert( vars.begin(), vars.end() );
                        conjInconsistent = true;
                        break;
                    }
                    else if( conflictingWithSolutionSpace == 1 )
                        cons = (*conj).erase( cons );
                    else
                        ++cons;
                }
            }
            bool conjEmpty = (*conj).empty();
            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
            {
                // Delete the conjunction.
                conj->clear();
                conj = _toSimplify.erase( conj );
            }
            else
                ++conj;
            if( !containsEmptyDisjunction && conjEmpty )
                containsEmptyDisjunction = true;
        }
    }

    bool splitProducts( DisjunctionOfConstraintConjunctions& _toSimplify, bool _onlyNeq )
    {
        bool result = true;
        size_t toSimpSize = _toSimplify.size();
        for( size_t pos = 0; pos < toSimpSize; )
        {
            if( !_toSimplify.begin()->empty() )
            {
                DisjunctionOfConstraintConjunctions temp;
                if( !splitProducts( _toSimplify[pos], temp, _onlyNeq ) )
                    result = false;
                _toSimplify.erase( _toSimplify.begin() );
                _toSimplify.insert( _toSimplify.end(), temp.begin(), temp.end() );
                --toSimpSize;
            }
            else
                ++pos;
        }
        return result;
    }

    bool splitProducts( const ConstraintVector& _toSimplify, DisjunctionOfConstraintConjunctions& _result, bool _onlyNeq )
    {
        std::vector<DisjunctionOfConstraintConjunctions> toCombine;
        for( auto constraint = _toSimplify.begin(); constraint != _toSimplify.end(); ++constraint )
        {
            auto& factorization = (*constraint).lhs_factorization();
            if( !carl::is_trivial(factorization) )
            {
                switch( constraint->relation() )
                {
                    case Relation::EQ:
                    {
                        if( !_onlyNeq )
                        {
                            toCombine.emplace_back();
                            for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                            {
                                toCombine.back().emplace_back();
                                toCombine.back().back().push_back( smtrat::ConstraintT( factor->first, Relation::EQ ) );
                            }
                            simplify( toCombine.back() );
                        }
                        else
                        {
                            toCombine.emplace_back();
                            toCombine.back().emplace_back();
                            toCombine.back().back().push_back( *constraint );
                        }
                        break;
                    }
                    case Relation::NEQ:
                    {
                        toCombine.emplace_back();
                        toCombine.back().emplace_back();
                        for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                            toCombine.back().back().push_back( smtrat::ConstraintT( factor->first, Relation::NEQ ) );
                        simplify( toCombine.back() );
                        break;
                    }
                    default:
                    {
                        if( !_onlyNeq )
                        {
                            toCombine.push_back( getSignCombinations( *constraint ) );
                            simplify( toCombine.back() );
                        }
                        else
                        {
                            toCombine.emplace_back();
                            toCombine.back().emplace_back();
                            toCombine.back().back().push_back( *constraint );
                        }
                    }
                }
            }
            else
            {
                toCombine.emplace_back();
                toCombine.back().emplace_back();
                toCombine.back().back().push_back( *constraint );
            }
        }
        bool result = true;
        if( !combine( toCombine, _result ) )
            result = false;
        simplify( _result );
        return result;
    }

    DisjunctionOfConstraintConjunctions splitProducts( const smtrat::ConstraintT& _constraint, bool _onlyNeq )
    {
        DisjunctionOfConstraintConjunctions result;
        auto& factorization = _constraint.lhs_factorization();
        if( !carl::is_trivial(factorization) )
        {
            switch( _constraint.relation() )
            {
                case Relation::EQ:
                {
                    if( !_onlyNeq )
                    {
                        for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                        {
                            result.emplace_back();
                            result.back().push_back( smtrat::ConstraintT( factor->first, Relation::EQ ) );
                        }
                    }
                    else
                    {
                        result.emplace_back();
                        result.back().push_back( _constraint );
                    }
                    simplify( result );
                    break;
                }
                case Relation::NEQ:
                {
                    result.emplace_back();
                    for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
                        result.back().push_back( smtrat::ConstraintT( factor->first, Relation::NEQ ) );
                    simplify( result );
                    break;
                }
                default:
                {
                    if( !_onlyNeq )
                    {
                        result = getSignCombinations( _constraint );
                        simplify( result );
                    }
                    else
                    {
                        result.emplace_back();
                        result.back().push_back( _constraint );
                    }
                }
                
            }
        }
        else
        {
            result.emplace_back();
            result.back().push_back( _constraint );
        }
        return result;
    }

    void splitSosDecompositions( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
        // TODO this needs to be reviewed and fixed
        // It seems that is is assumed that lcoeffNeg * constraint.lhs() is positive if
        // a SOS decomposition exists. However, we can only follow that it's non-negative
        // (in the univariate case), for the multivariate case more requirements need to be made
        // (therefor constraint.lhs().hasConstantTerm() ???).
        // This lead to wrong simplifications in very rare cases, for example
        // -100 + 140*z + -49*y^2 + -49*z^2 is wrongly simplified to true (see McsatVSBug).
        
        // Temporarily disabled (what can be followed in the multivariate case?).
        return;

        for( size_t i = 0; i < _toSimplify.size(); )
        {
            auto& cc = _toSimplify[i];
            bool foundNoInvalidConstraint = true;
            size_t pos = 0;
            while( foundNoInvalidConstraint && pos < cc.size() )
            {
                const smtrat::ConstraintT& constraint = cc[pos];
                std::vector<std::pair<smtrat::Rational,smtrat::Poly>> sosDec;
                bool lcoeffNeg = carl::isNegative(constraint.lhs().lcoeff());
                if (lcoeffNeg)
                    sosDec = carl::sos_decomposition(-constraint.lhs());
                else
                    sosDec = carl::sos_decomposition(constraint.lhs());
                if( sosDec.size() > 1 )
                {
//                    std::cout << "Sum-of-squares decomposition of " << constraint.lhs() << " = " << sosDec << std::endl;
                    bool addSquares = true;
                    bool constraintValid = false;
                    switch( constraint.relation() )
                    {
                        case carl::Relation::EQ:
                        {
                            if( constraint.lhs().hasConstantTerm() )
                            {
                                foundNoInvalidConstraint = false;
                                addSquares = false;
                            }
                            break;
                        }
                        case carl::Relation::NEQ:
                        {
                            addSquares = false;
                            if( constraint.lhs().hasConstantTerm() )
                            {
                                constraintValid = true;
                            }
                            break;
                        }
                        case carl::Relation::LEQ:
                        {
                            if( lcoeffNeg )
                            {
                                addSquares = false;
                                constraintValid = true;
                            }
                            else if( constraint.lhs().hasConstantTerm() )
                            {
                                addSquares = false;
                                foundNoInvalidConstraint = false;
                            }
                            break;
                        }
                        case carl::Relation::LESS:
                        {
                            addSquares = false;
                            if( lcoeffNeg )
                            {
                                if( constraint.lhs().hasConstantTerm() )
                                    constraintValid = true;
                            }
                            else 
                                foundNoInvalidConstraint = false;
                            break;
                        }
                        case carl::Relation::GEQ:
                        {
                            if( !lcoeffNeg )
                            {
                                addSquares = false;
                                constraintValid = true;
                            }
                            else if( constraint.lhs().hasConstantTerm() )
                            {
                                addSquares = false;
                                foundNoInvalidConstraint = false;
                            }
                            break;
                        }
                        default:
                        {
                            assert( constraint.relation() == carl::Relation::GREATER );
                            addSquares = false;
                            if( lcoeffNeg )
                                foundNoInvalidConstraint = false;
                            else
                            {
                                if( constraint.lhs().hasConstantTerm() )
                                    constraintValid = true;
                            }
                        }
                    }
                    assert( !(!foundNoInvalidConstraint && constraintValid) );
                    assert( !(!foundNoInvalidConstraint && addSquares) );
                    if( constraintValid || addSquares )
                    {
                        cc[pos] = cc.back();
                        cc.pop_back();
                    }
                    else
                        ++pos;
                    if( addSquares )
                    {
                        for( auto it = sosDec.begin(); it != sosDec.end(); ++it )
                        {
                            cc.emplace_back( it->second, carl::Relation::EQ );
                        }
                    }   
                }
                else
                    ++pos;
            }
            if( foundNoInvalidConstraint )
                ++i;
            else
            {
                cc = _toSimplify.back();
                _toSimplify.pop_back();
            }
        }
    }

    DisjunctionOfConstraintConjunctions getSignCombinations( const smtrat::ConstraintT& _constraint )
    {
        DisjunctionOfConstraintConjunctions combinations;
        auto& factorization = _constraint.lhs_factorization();
        if( !carl::is_trivial(factorization) && factorization.size() <= MAX_PRODUCT_SPLIT_NUMBER )
        {
            assert( _constraint.relation() == Relation::GREATER || _constraint.relation() == Relation::LESS
                    || _constraint.relation() == Relation::GEQ || _constraint.relation() == Relation::LEQ );
            Relation relPos = Relation::GREATER;
            Relation relNeg = Relation::LESS;
            if( _constraint.relation() == Relation::GEQ || _constraint.relation() == Relation::LEQ )
            {
                relPos = Relation::GEQ;
                relNeg = Relation::LEQ;
            }
            bool positive = (_constraint.relation() == Relation::GEQ || _constraint.relation() == Relation::GREATER);
            ConstraintVector positives;
            ConstraintVector alwayspositives;
            ConstraintVector negatives;
            ConstraintVector alwaysnegatives;
            unsigned numOfAlwaysNegatives = 0;
            for( auto factor = factorization.begin(); factor != factorization.end(); ++factor )
            {
                smtrat::ConstraintT consPos = smtrat::ConstraintT( factor->first, relPos );
                unsigned posConsistent = consPos.isConsistent();
                if( posConsistent != 0 )
                    positives.push_back( consPos );
                smtrat::ConstraintT consNeg = smtrat::ConstraintT( factor->first, relNeg );
                unsigned negConsistent = consNeg.isConsistent();
                if( negConsistent == 0 )
                {
                    if( posConsistent == 0 )
                    {
                        combinations.emplace_back();
                        combinations.back().push_back( consNeg );
                        return combinations;
                    }
                    if( posConsistent != 1 )
                        alwayspositives.push_back( positives.back() );
                    positives.pop_back();
                }
                else
                {
                    if( posConsistent == 0 )
                    {
                        ++numOfAlwaysNegatives;
                        if( negConsistent != 1 ) 
                            alwaysnegatives.push_back( consNeg );
                    }
                    else negatives.push_back( consNeg );
                }
            }
            assert( positives.size() == negatives.size() );
            if( positives.size() > 0 )
            {
                std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> > combSelector = std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >();
                if( fmod( numOfAlwaysNegatives, 2.0 ) != 0.0 )
                {
                    if( positive ) 
                        getOddBitStrings( positives.size(), combSelector );
                    else 
                        getEvenBitStrings( positives.size(), combSelector );
                }
                else
                {
                    if( positive ) 
                        getEvenBitStrings( positives.size(), combSelector );
                    else 
                        getOddBitStrings( positives.size(), combSelector );
                }
                for( auto comb = combSelector.begin(); comb != combSelector.end(); ++comb )
                {
                    combinations.emplace_back( alwaysnegatives );
                    combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
                    for( unsigned pos = 0; pos < positives.size(); ++pos )
                    {
                        if( (*comb)[pos] ) 
                            combinations.back().push_back( negatives[pos] );
                        else 
                            combinations.back().push_back( positives[pos] );
                    }
                }
            }
            else
            {
                combinations.emplace_back( alwaysnegatives );
                combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
            }
        }
        else
        {
            combinations.emplace_back();
            combinations.back().push_back( _constraint );
        }
        return combinations;
    }

    void getOddBitStrings( std::size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings )
    {
        assert( _length > 0 );
        if( _length == 1 )  _strings.push_back( std::bitset<MAX_PRODUCT_SPLIT_NUMBER>( 1 ) );
        else
        {
            std::size_t pos = _strings.size();
            getEvenBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos )
            {
                _strings[pos] <<= 1;
                _strings[pos].flip(0);
            }
            getOddBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos ) _strings[pos] <<= 1;
        }
    }

    void getEvenBitStrings( std::size_t _length, std::vector< std::bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings )
    {
        assert( _length > 0 );
        if( _length == 1 ) _strings.push_back( std::bitset<MAX_PRODUCT_SPLIT_NUMBER>( 0 ) );
        else
        {
            std::size_t pos = _strings.size();
            getEvenBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos ) _strings[pos] <<= 1;
            getOddBitStrings( _length - 1, _strings );
            for( ; pos < _strings.size(); ++pos )
            {
                _strings[pos] <<= 1;
                _strings[pos].flip(0);
            }
        }
    }

    void print( DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        auto conj = _substitutionResults.begin();
        while( conj != _substitutionResults.end() )
        {
            if( conj != _substitutionResults.begin() )
                std::cout << " or (";
            else
                std::cout << "    (";
            auto cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( cons != (*conj).begin() )
                    std::cout << " and ";
                std::cout << *cons;
                cons++;
            }
            std::cout << ")" << std::endl;
            conj++;
        }
        std::cout << std::endl;
    }
    
    bool substitute( const smtrat::ConstraintT& _cons,
                     const Substitution& _subs,
                     DisjunctionOfConstraintConjunctions& _result,
                     bool _accordingPaper,
                     Variables& _conflictingVariables,
                     const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        #ifdef VS_DEBUG_SUBSTITUTION
        std::cout << "substitute: ( " << _cons << " )" << _subs << std::endl;
        #endif
        bool result = true;
        // Apply the substitution according to its type.
        switch( _subs.type() )
        {
            case Substitution::NORMAL:
            {
                result = substituteNormal( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::PLUS_EPSILON:
            {
                result = substitutePlusEps( _cons, _subs, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::MINUS_INFINITY:
            {
                substituteInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            case Substitution::PLUS_INFINITY:
            {
                substituteInf( _cons, _subs, _result, _conflictingVariables, _solutionSpace );
                break;
            }
            default:
            {
                std::cout << "Error in substitute: unexpected type of substitution." << std::endl;
            }
        }
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        bool factorization = true;
        if( factorization && !splitProducts( _result, true ) ) 
            result = false;
        if( result )
        {
            splitSosDecompositions( _result );
        }
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _result );
        #endif
        return result;
    }

    bool substituteNormal( const smtrat::ConstraintT& _cons,
                           const Substitution& _subs,
                           DisjunctionOfConstraintConjunctions& _result,
                           bool _accordingPaper,
                           Variables& _conflictingVariables,
                           const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        
        bool result = true;
        if( _cons.variables().has( _subs.variable() ) )
        {
            // Collect all necessary left hand sides to create the new conditions of all cases referring to the virtual substitution.
            if( carl::pow( smtrat::Rational(smtrat::Rational(_subs.term().constantPart().size()) + smtrat::Rational(_subs.term().factor().size()) * smtrat::Rational(_subs.term().radicand().size())), _cons.maxDegree( _subs.variable() )) > (MAX_NUM_OF_TERMS*MAX_NUM_OF_TERMS) )
            {
                return false;
            }
            smtrat::SqrtEx sub = carl::substitute( _cons.lhs(), _subs.variable(), _subs.term() );
            #ifdef VS_DEBUG_SUBSTITUTION
            std::cout << "Result of common substitution:" << sub << std::endl;
            #endif
            // The term then looks like:    q/s
            if( !sub.has_sqrt() )
            {
                // Create the new decision tuples.
                if( _cons.relation() == Relation::EQ || _cons.relation() == Relation::NEQ )
                {
                    // Add conjunction (sub.constantPart() = 0) to the substitution result.
                    _result.emplace_back();
                    _result.back().push_back( smtrat::ConstraintT( sub.constantPart(), _cons.relation() ) );
                }
                else
                {
                    if( !_subs.term().denominator().isConstant() )
                    {
                        // Add conjunction (sub.denominator()>0 and sub.constantPart() </>/<=/>= 0) to the substitution result.
                        _result.emplace_back();
                        _result.back().push_back( smtrat::ConstraintT( sub.denominator(), Relation::GREATER ) );
                        _result.back().push_back( smtrat::ConstraintT( sub.constantPart(), _cons.relation() ) );
                        // Add conjunction (sub.denominator()<0 and sub.constantPart() >/</>=/<= 0) to the substitution result.
                        Relation inverseRelation;
                        switch( _cons.relation() )
                        {
                            case Relation::LESS:
                                inverseRelation = Relation::GREATER;
                                break;
                            case Relation::GREATER:
                                inverseRelation = Relation::LESS;
                                break;
                            case Relation::LEQ:
                                inverseRelation = Relation::GEQ;
                                break;
                            case Relation::GEQ:
                                inverseRelation = Relation::LEQ;
                                break;
                            default:
                                assert( false );
                                inverseRelation = Relation::EQ;
                        }
                        _result.emplace_back();
                        _result.back().push_back( smtrat::ConstraintT( sub.denominator(), Relation::LESS ) );
                        _result.back().push_back( smtrat::ConstraintT( sub.constantPart(), inverseRelation ) );
                    }
                    else
                    {
                        // Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                        _result.emplace_back();
                        _result.back().push_back( smtrat::ConstraintT( sub.constantPart(), _cons.relation() ) );
                    }
                }
            }
            // The term then looks like:   (q+r*sqrt(b^2-4ac))/s
            else
            {
                smtrat::Poly s = Poly(1);
                if( !_subs.term().denominator().isConstant() )
                    s = sub.denominator();
                switch( _cons.relation() )
                {
                    case Relation::EQ:
                    {
                        result = substituteNormalSqrtEq( sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case Relation::NEQ:
                    {
                        result = substituteNormalSqrtNeq( sub.radicand(), sub.constantPart(), sub.factor(), _result, _accordingPaper );
                        break;
                    }
                    case Relation::LESS:
                    {
                        result = substituteNormalSqrtLess( sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case Relation::GREATER:
                    {
                        result = substituteNormalSqrtLess( sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
                        break;
                    }
                    case Relation::LEQ:
                    {
                        result = substituteNormalSqrtLeq( sub.radicand(), sub.constantPart(), sub.factor(), s, _result, _accordingPaper );
                        break;
                    }
                    case Relation::GEQ:
                    {
                        result = substituteNormalSqrtLeq( sub.radicand(), sub.constantPart(), sub.factor(), -s, _result, _accordingPaper );
                        break;
                    }
                    default:
                        std::cout << "Error in substituteNormal: Unexpected relation symbol" << std::endl;
                        assert( false );
                }
            }
        }
        else
        {
            _result.emplace_back();
            _result.back().push_back( _cons );
        }
        simplify( _result, _conflictingVariables, _solutionSpace );
        return result;
    }

    bool substituteNormalSqrtEq( const smtrat::Poly& _radicand,
                                 const smtrat::Poly& _q,
                                 const smtrat::Poly& _r,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper )
    {
        if( _q.size() > MAX_NUM_OF_TERMS || _r.size() > MAX_NUM_OF_TERMS || _radicand.size() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Poly lhs = carl::pow(_q, 2) - carl::pow(_r, 2) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Poly qr = _q * _r;
            // Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( qr, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::EQ ) );
        }
        else
        {
            // Add conjunction (q=0 and r=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::EQ ) );
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::EQ ) );
            // Add conjunction (q=0 and radicand=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::EQ ) );
            _result.back().push_back( smtrat::ConstraintT( _radicand, Relation::EQ ) );
            // Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::EQ ) );
            // Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::EQ ) );
        }
        return true;
    }

    bool substituteNormalSqrtNeq( const smtrat::Poly& _radicand,
                                  const smtrat::Poly& _q,
                                  const smtrat::Poly& _r,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        if( _q.size() > MAX_NUM_OF_TERMS || _r.size() > MAX_NUM_OF_TERMS || _radicand.size() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Poly lhs = carl::pow(_q, 2) - carl::pow(_r, 2) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Poly qr = _q * _r;
            // Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( qr, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::NEQ ) );
        }
        else
        {
            // Add conjunction (q>0 and r>0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::GREATER ) );
            // Add conjunction (q<0 and r<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::LESS ) );
            // Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::NEQ ) );
        }
        return true;
    }

    bool substituteNormalSqrtLess( const smtrat::Poly& _radicand,
                                   const smtrat::Poly& _q,
                                   const smtrat::Poly& _r,
                                   const smtrat::Poly& _s,
                                   DisjunctionOfConstraintConjunctions& _result,
                                   bool _accordingPaper )
    {
        if( _q.size() > MAX_NUM_OF_TERMS || _r.size() > MAX_NUM_OF_TERMS || _radicand.size() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Poly lhs = carl::pow(_q, 2) - carl::pow(_r, 2) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Poly qs = _q * _s;
            smtrat::Poly rs = _r * _s;
            // Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( qs, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GREATER ) );
            // Add conjunction (r*s<=0 and q*s<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( rs, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( qs, Relation::LESS ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( rs, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LESS ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GREATER ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GREATER ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LESS ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LESS ) );
            // Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::GEQ ) );
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::LESS ) );
            // Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::GREATER ) );
        }
        return true;
    }

    bool substituteNormalSqrtLeq( const smtrat::Poly& _radicand,
                                  const smtrat::Poly& _q,
                                  const smtrat::Poly& _r,
                                  const smtrat::Poly& _s,
                                  DisjunctionOfConstraintConjunctions& _result,
                                  bool _accordingPaper )
    {
        if( _q.size() > MAX_NUM_OF_TERMS || _r.size() > MAX_NUM_OF_TERMS || _radicand.size() > MAX_NUM_OF_TERMS )
            return false;
        smtrat::Poly lhs = carl::pow(_q, 2) - carl::pow(_r, 2) * _radicand;
        if( _accordingPaper )
        {
            smtrat::Poly qs = _q * _s;
            smtrat::Poly rs = _r * _s;
            // Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( qs, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GEQ ) );
            // Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( rs, Relation::LEQ ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LEQ ) );
        }
        else
        {
            // Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GEQ ) );
            // Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::GEQ ) );
            // Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LEQ ) );
            // Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::LESS ) );
            _result.back().push_back( smtrat::ConstraintT( _s, Relation::GREATER ) );
            _result.back().push_back( smtrat::ConstraintT( lhs, Relation::LEQ ) );
            // Add conjunction (r=0 and q=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _r, Relation::EQ ) );
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::EQ ) );
            // Add conjunction (radicand=0 and q=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _radicand, Relation::EQ ) );
            _result.back().push_back( smtrat::ConstraintT( _q, Relation::EQ ) );
        }
        return true;
    }

    bool substitutePlusEps( const smtrat::ConstraintT& _cons,
                            const Substitution& _subs,
                            DisjunctionOfConstraintConjunctions& _result,
                            bool _accordingPaper,
                            Variables& _conflictingVariables,
                            const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        bool result = true;
        if( !_cons.variables().empty() )
        {
            if( _cons.variables().has( _subs.variable() ) )
            {
                switch( _cons.relation() )
                {
                    case Relation::EQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case Relation::NEQ:
                    {
                        substituteNotTrivialCase( _cons, _subs, _result );
                        break;
                    }
                    case Relation::LESS:
                    {
                        result = substituteEpsGradients( _cons, _subs, Relation::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case Relation::GREATER:
                    {
                        result = substituteEpsGradients( _cons, _subs, Relation::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case Relation::LEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, Relation::LESS, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    case Relation::GEQ:
                    {
                        substituteTrivialCase( _cons, _subs, _result );
                        result = substituteEpsGradients( _cons, _subs, Relation::GREATER, _result, _accordingPaper, _conflictingVariables, _solutionSpace );
                        break;
                    }
                    default:
                        assert( false );
                }
                simplify( _result, _conflictingVariables, _solutionSpace );
            }
            else
            {
                _result.emplace_back();
                _result.back().push_back( _cons );
            }
        }
        else
        {
            assert( false );
            std::cerr << "Warning in substitutePlusEps: The chosen constraint has no variable" << std::endl;
        }
        return result;
    }

    bool substituteEpsGradients( const smtrat::ConstraintT& _cons,
                                 const Substitution& _subs,
                                 const Relation _relation,
                                 DisjunctionOfConstraintConjunctions& _result,
                                 bool _accordingPaper,
                                 Variables& _conflictingVariables,
                                 const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        assert( _cons.variables().has( _subs.variable() ) );
        // Create a substitution formed by the given one without an addition of epsilon.
        Substitution substitution = Substitution( _subs.variable(), _subs.term(), Substitution::NORMAL, carl::PointerSet<Condition>(_subs.originalConditions()) );
        // Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],  where the parameter relation is ~.
        smtrat::ConstraintT firstCaseInequality = smtrat::ConstraintT( _cons.lhs(), _relation );
        if( !substituteNormal( firstCaseInequality, substitution, _result, _accordingPaper, _conflictingVariables, _solutionSpace ) )
            return false;
        // Create a vector to store the results of each single substitution.
        std::vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        /*
         * Let k be the maximum degree of x in f, then call for every 1<=i<=k substituteNormal with:
         *
         *      f^0(x)=0 and ... and f^i-1(x)=0 and f^i(x)~0     as constraints and
         *      [x -> t]                                         as substitution,
         *
         * where the relation is ~.
         */
        smtrat::Poly deriv = smtrat::Poly( _cons.lhs() );
        while( deriv.has( _subs.variable() ) )
        {
            // Change the relation symbol of the last added constraint to "=".
            smtrat::ConstraintT equation = smtrat::ConstraintT( deriv, Relation::EQ );
            // Form the derivate of the left hand side of the last added constraint.
            deriv = carl::derivative(deriv, _subs.variable(), 1);
            // Add the constraint f^i(x)~0.
            smtrat::ConstraintT inequality = smtrat::ConstraintT( deriv, _relation );
            // Apply the substitution (without epsilon) to the new constraints.
            substitutionResultsVector.emplace_back();
            if( !substituteNormal( equation, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace ) )
                return false;
            substitutionResultsVector.emplace_back();
            if( !substituteNormal( inequality, substitution, substitutionResultsVector.back(), _accordingPaper, _conflictingVariables, _solutionSpace ) )
                return false;
            if( !combine( substitutionResultsVector, _result ) )
                return false;
            simplify( _result, _conflictingVariables, _solutionSpace );
            // Remove the last substitution result.
            substitutionResultsVector.pop_back();
        }
        return true;
    }

    void substituteInf( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result, Variables& _conflictingVariables, const smtrat::EvalDoubleIntervalMap& _solutionSpace )
    {
        if( !_cons.variables().empty() )
        {
            if( _cons.variables().has( _subs.variable() ) )
            {
                if( _cons.relation() == Relation::EQ )
                    substituteTrivialCase( _cons, _subs, _result );
                else if( _cons.relation() == Relation::NEQ )
                    substituteNotTrivialCase( _cons, _subs, _result );
                else
                             
                    substituteInfLessGreater( _cons, _subs, _result );
                simplify( _result, _conflictingVariables, _solutionSpace );
            }
            else
            {
                _result.emplace_back();
                _result.back().push_back( _cons );
            }
        }
        else
            std::cout << "Warning in substituteInf: The chosen constraint has no variable" << std::endl;
    }

    void substituteInfLessGreater( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons.relation() != Relation::EQ );
        assert( _cons.relation() != Relation::NEQ );
        // Determine the relation for the coefficients of the odd and even degrees.
        Relation oddRelationType  = Relation::GREATER;
        Relation evenRelationType = Relation::LESS;
        if( _subs.type() == Substitution::MINUS_INFINITY )
        {
            if( _cons.relation() == Relation::GREATER || _cons.relation() == Relation::GEQ )
            {
                oddRelationType  = Relation::LESS;
                evenRelationType = Relation::GREATER;
            }
        }
        else
        {
            assert( _subs.type() == Substitution::PLUS_INFINITY );
            if( _cons.relation() == Relation::LESS || _cons.relation() == Relation::LEQ )
            {
                oddRelationType  = Relation::LESS;
                evenRelationType = Relation::GREATER;
            }
        }
        // Check all cases according to the substitution rules.
        carl::uint varDegree = _cons.maxDegree( _subs.variable() );
        assert( varDegree > 0 );
        for( carl::uint i = varDegree + 1; i > 0; --i )
        {
            // Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
            _result.emplace_back();
            for( carl::uint j = varDegree; j > i - 1; --j )
                _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), j ), Relation::EQ ) );
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                    _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), i - 1 ), oddRelationType ) );
                else
                    _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), i - 1 ), evenRelationType ) );
            }
            else
                _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), i - 1 ), _cons.relation() ) );
        }
    }

    void substituteTrivialCase( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons.relation() == Relation::EQ || _cons.relation() == Relation::LEQ || _cons.relation() == Relation::GEQ );
        carl::uint varDegree = _cons.maxDegree( _subs.variable() );
        // Check the cases (a_0=0 and ... and a_n=0)
        _result.emplace_back();
        for( carl::uint i = 0; i <= varDegree; ++i )
            _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), i ), Relation::EQ ) );
    }

    void substituteNotTrivialCase( const smtrat::ConstraintT& _cons, const Substitution& _subs, DisjunctionOfConstraintConjunctions& _result )
    {
        assert( _cons.relation() == Relation::NEQ );
        carl::uint varDegree = _cons.maxDegree( _subs.variable() );
        for( carl::uint i = 0; i <= varDegree; ++i )
        {
            // Add conjunction (a_i!=0) to the substitution result.
            _result.emplace_back();
            _result.back().push_back( smtrat::ConstraintT( _cons.coefficient( _subs.variable(), i ), Relation::NEQ ) );
        }
    }
}    // end namspace vs
}
