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
 * Constraint.cpp
 * 
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @author Ulrich Loup
 * @since 2010-04-26
 * @version 2013-10-21
 */

#include "Constraint.h"
#ifdef USE_GINAC
#include "carl/converter/GinacConverter.h"
#endif

using namespace std;
using namespace carl;

namespace smtrat
{
    Constraint::Constraint():
        mID( 0 ),
        mHash( CONSTRAINT_HASH( ZERO_POLYNOMIAL, Relation::EQ ) ), 
        mRelation( Relation::EQ ),
        mLhs( Rational( 0 ) ),
        mFactorization(),
        mVariables(),
        mVarInfoMap(),
        mLhsDefinitess( carl::Definiteness::NON )
    {}

    Constraint::Constraint( const Polynomial& _lhs, const Relation _rel, unsigned _id ):
        mID( _id ),
        mHash( CONSTRAINT_HASH( _lhs, _rel ) ),
        mRelation( _rel ),
        mLhs( _lhs ),
        mFactorization(),
        mVariables(),
        mVarInfoMap(),
        mLhsDefinitess( carl::Definiteness::NON )
    {
        mLhs.gatherVariables( mVariables );
        
        if( hasIntegerValuedVariable() && !hasRealValuedVariable() )
        {
            if( relation() == Relation::LESS )
            {
                mLhs = mLhs + ONE_RATIONAL;
                mRelation = Relation::LEQ;
                mHash = CONSTRAINT_HASH( mLhs, mRelation );
            }
            if( relation() == Relation::GREATER )
            {
                mLhs = mLhs - ONE_RATIONAL;
                mRelation = Relation::GEQ;
                mHash = CONSTRAINT_HASH( mLhs, mRelation );
            }
        }
        carl::VariablesInformation<false,Polynomial> varinfos = mLhs.getVarInfo<false>();
        for( auto varInfo = varinfos.begin(); varInfo != varinfos.end(); ++varInfo )
            mVarInfoMap.emplace_hint( mVarInfoMap.end(), *varInfo );
        mLhsDefinitess = mLhs.definiteness();
    }

    Constraint::Constraint( const Constraint& _constraint, bool _rehash ):
        mID( _constraint.id() ),
        mHash( _rehash ? CONSTRAINT_HASH( _constraint.lhs(), _constraint.relation() ) : _constraint.getHash() ),
        mRelation( _constraint.relation() ),
        mLhs( _constraint.mLhs ),
        mFactorization( _constraint.mFactorization ),
        mVariables( _constraint.variables() ),
        mVarInfoMap( _constraint.mVarInfoMap ),
        mLhsDefinitess( _constraint.mLhsDefinitess )
    {}

    Constraint::~Constraint()
    {}
    
    unsigned Constraint::satisfiedBy( const EvalRationalMap& _assignment ) const
    {
//        std::cout << "Is  " << this->toString( 0, true, true ) << std::endl;
//        std::cout << "satisfied by  " << std::endl;
//        for( auto iter = _assignment.begin(); iter != _assignment.end(); ++iter )
//            std::cout << iter->first << " in " << iter->second << std::endl;
        unsigned result = 2;
        Polynomial tmp = mLhs.substitute( _assignment );
        if( tmp.isConstant() )
            result = evaluate( (tmp.isZero() ? ZERO_RATIONAL : tmp.trailingTerm()->coeff()), relation() ) ? 1 : 0;
//        std::cout << "result is " << result << std::endl;
//        std::cout << std::endl;
        return result;
    }

    unsigned Constraint::isConsistent() const
    {
        if( variables().empty() )
            return evaluate( constantPart(), relation() ) ? 1 : 0;
        else
        {
            switch( relation() )
            {
                case Relation::EQ:
                {
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE || mLhsDefinitess == carl::Definiteness::NEGATIVE ) return 0;
                    break;
                }
                case Relation::NEQ:
                {
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE || mLhsDefinitess == carl::Definiteness::NEGATIVE ) return 1;
                    break;
                }
                case Relation::LESS:
                {
                    if( mLhsDefinitess == carl::Definiteness::NEGATIVE ) return 1;
                    if( mLhsDefinitess >= carl::Definiteness::POSITIVE_SEMI ) return 0;
                    break;
                }
                case Relation::GREATER:
                {
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE ) return 1;
                    if( mLhsDefinitess <= carl::Definiteness::NEGATIVE_SEMI ) return 0;
                    break;
                }
                case Relation::LEQ:
                {
                    if( mLhsDefinitess <= carl::Definiteness::NEGATIVE_SEMI ) return 1;
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE ) return 0;
                    break;
                }
                case Relation::GEQ:
                {
                    if( mLhsDefinitess >= carl::Definiteness::POSITIVE_SEMI ) return 1;
                    if( mLhsDefinitess == carl::Definiteness::NEGATIVE ) return 0;
                    break;
                }
                default:
                {
                    cout << "Error in isConsistent: unexpected relation symbol." << endl;
                    return false;
                }
            }
            return 2;
        }
    }
    
    unsigned Constraint::consistentWith( const EvalDoubleIntervalMap& _solutionInterval ) const
    {
        if( variables().empty() )
            return evaluate( constantPart(), relation() ) ? 1 : 0;
        else
        {
            auto comp = []( const Variable& a, const pair<Variable, DoubleInterval>& b) { return a == b.first; };
            if( !std::equal( variables().begin(), variables().end(), _solutionInterval.begin(), comp ) )
            {
                return 2;
            }
            DoubleInterval solutionSpace = carl::IntervalEvaluation::evaluate( mLhs, _solutionInterval );
            if( solutionSpace.isEmpty() )
                return 2;
            switch( relation() )
            {
                case Relation::EQ:
                {
                    if( solutionSpace.isZero() )
                        return 1;
                    else if( !solutionSpace.contains( 0 ) )
                        return 0;
                    break;
                }
                case Relation::NEQ:
                {
                    if( !solutionSpace.contains( 0 ) )
                        return 1;
                    break;
                }
                case Relation::LESS:
                {
                    if( solutionSpace.upperBoundType() != carl::BoundType::INFTY )
                    {
                        if( solutionSpace.upper() < 0 )
                            return 1;
                        else if( solutionSpace.upper() == 0 && solutionSpace.upperBoundType() == carl::BoundType::STRICT )
                            return 1;
                    }
                    if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY && solutionSpace.lower() >= 0 )
                        return 0;
                    break;
                }
                case Relation::GREATER:
                {
                    if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY )
                    {
                        if( solutionSpace.lower() > 0 )
                            return 1;
                        else if( solutionSpace.lower() == 0 && solutionSpace.lowerBoundType() == carl::BoundType::STRICT )
                            return 1;
                    }
                    if( solutionSpace.upperBoundType() != carl::BoundType::INFTY && solutionSpace.upper() <= 0 )
                        return 0;
                    break;
                }
                case Relation::LEQ:
                {
                    if( solutionSpace.upperBoundType() != carl::BoundType::INFTY && solutionSpace.upper() <= 0)
                        return 1;
                    if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY )
                    {
                        if( solutionSpace.lower() > 0 )
                            return 0;
                        else if( solutionSpace.lower() == 0 && solutionSpace.lowerBoundType() == carl::BoundType::STRICT )
                            return 0;
                    }
                    break;
                }
                case Relation::GEQ:
                {
                    if( solutionSpace.lowerBoundType() != carl::BoundType::INFTY && solutionSpace.lower() >= 0 )
                        return 1;
                    if( solutionSpace.upperBoundType() != carl::BoundType::INFTY )
                    {
                        if( solutionSpace.upper() < 0 )
                            return 0;
                        else if( solutionSpace.upper() == 0 && solutionSpace.upperBoundType() == carl::BoundType::STRICT )
                            return 0;
                    }
                    break;
                }
                default:
                {
                    cout << "Error in isConsistent: unexpected relation symbol." << endl;
                    return 0;
                }
            }
            return 2;
        }
    }
    
    bool Constraint::hasFinitelyManySolutionsIn( const carl::Variable& _var ) const
    {
        if( variables().find( _var ) == variables().end() )
            return true;
        if( relation() == Relation::EQ )
        {
            if( variables().size() == 1 )
                return true;
            //TODO: else, if not too expensive (construct constraints being the side conditions)
        }
        return false;
    }

    Polynomial Constraint::coefficient( const carl::Variable& _var, unsigned _degree ) const
    {
        auto varInfo = mVarInfoMap.find( _var );
        assert( varInfo != mVarInfoMap.end() );
        if( !varInfo->second.hasCoeff() )
        {
            varInfo->second = mLhs.getVarInfo<true>( _var );
        }
        auto d = varInfo->second.coeffs().find( _degree );
        return d != varInfo->second.coeffs().end() ? d->second : ZERO_POLYNOMIAL;
    }

    bool Constraint::getSubstitution( carl::Variable& _substitutionVariable, Polynomial& _substitutionTerm ) const
    {
        if( mRelation != Relation::EQ )
            return false;
        for( map<carl::Variable, VarInfo>::iterator varInfoPair = mVarInfoMap.begin(); varInfoPair != mVarInfoMap.end(); ++varInfoPair )
        {
            if( varInfoPair->second.maxDegree() == 1 )
            {
                if( !varInfoPair->second.hasCoeff() )
                {
                    varInfoPair->second = mLhs.getVarInfo<true>( varInfoPair->first );
                }
                auto d = varInfoPair->second.coeffs().find( 1 );
                assert( d != varInfoPair->second.coeffs().end() );
                _substitutionVariable = varInfoPair->first;
                _substitutionTerm = Polynomial( _substitutionVariable ) * d->second - mLhs;
                _substitutionTerm /= d->second.constantPart();
                return true;
            }
        }
        return false;
    }
    
    Constraint* Constraint::simplify() const
    {
        Relation rel = mRelation;
        if( (mLhsDefinitess == carl::Definiteness::POSITIVE_SEMI && rel == Relation::LEQ) || (mLhsDefinitess == carl::Definiteness::NEGATIVE_SEMI && rel == Relation::GEQ) )
            rel = Relation::EQ;
        // Left-hand side is a non-linear univariate monomial
        if( mVariables.size() == 1 && !mLhs.isLinear() && mLhs.nrTerms() == 1 )
        {
            switch( rel )
            {
                case Relation::EQ:
                    return new Constraint( Polynomial( *mVariables.begin() ), rel );
                case Relation::NEQ:
                    return new Constraint( Polynomial( *mVariables.begin() ), rel );
                case Relation::LEQ:
                    if( mLhsDefinitess == carl::Definiteness::NEGATIVE_SEMI )
                        return new Constraint( MINUS_ONE_POLYNOMIAL * Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() ), rel );
                    else
                        return new Constraint( (mLhs.trailingTerm()->coeff() > 0 ? ONE_POLYNOMIAL : MINUS_ONE_POLYNOMIAL ) * Polynomial( *mVariables.begin() ), rel );
                case Relation::GEQ:
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE_SEMI )
                        return new Constraint( Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() ), rel );
                    else
                        return new Constraint( (mLhs.trailingTerm()->coeff() > 0 ? ONE_POLYNOMIAL : MINUS_ONE_POLYNOMIAL ) * Polynomial( *mVariables.begin() ), rel );
                case Relation::LESS:
                    if( mLhsDefinitess == carl::Definiteness::NEGATIVE_SEMI )
                        return new Constraint( Polynomial( *mVariables.begin() ), Relation::NEQ );
                    else
                    {
                        if( mLhsDefinitess == carl::Definiteness::POSITIVE_SEMI )
                            return new Constraint( Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() ), rel );
                        else
                            return new Constraint( (mLhs.trailingTerm()->coeff() > 0 ? ONE_POLYNOMIAL : MINUS_ONE_POLYNOMIAL ) * Polynomial( *mVariables.begin() ), rel );
                    }
                case Relation::GREATER:
                    if( mLhsDefinitess == carl::Definiteness::POSITIVE_SEMI )
                        return new Constraint( Polynomial( *mVariables.begin() ), Relation::NEQ );
                    else
                    {
                        if( mLhsDefinitess == carl::Definiteness::NEGATIVE_SEMI )
                            return new Constraint( MINUS_ONE_POLYNOMIAL * Polynomial( *mVariables.begin() ) * Polynomial( *mVariables.begin() ), rel ); 
                        else
                            return new Constraint( (mLhs.trailingTerm()->coeff() > 0 ? ONE_POLYNOMIAL : MINUS_ONE_POLYNOMIAL ) * Polynomial( *mVariables.begin() ), rel ); 
                    }
                default:
                    assert( false );
            }
        }
        else if( hasIntegerValuedVariable() && !hasRealValuedVariable() && !lhs().isConstant() )
        {
            if( lhs().constantPart() != ZERO_RATIONAL )
            {
                // Find the gcd of the coefficients of the non-constant terms.
                auto term = lhs().rbegin();
                assert( !(*term)->isConstant() && carl::isInteger( (*term)->coeff() ) );
                Rational g = carl::abs( (*term)->coeff() );
                ++term;
                for( ; term != lhs().rend(); ++term )
                {
                    if( !(*term)->isConstant() )
                    {
                        assert( carl::isInteger( (*term)->coeff() ) );
                        g = carl::gcd( carl::getNum( g ), carl::getNum( carl::abs( (*term)->coeff() ) ) );
                    }
                }
                assert( g > ZERO_RATIONAL );
                if( carl::mod( carl::getNum( lhs().constantPart() ), carl::getNum( g ) ) != 0 )
                {
                    switch( relation() )
                    {
                        case Relation::EQ:
                            return new Constraint( ZERO_POLYNOMIAL, Relation::LESS );
                        case Relation::NEQ:
                            return new Constraint( ZERO_POLYNOMIAL, Relation::EQ );
                        case Relation::LEQ:
                        {
                            Polynomial newLhs = ((lhs() - lhs().constantPart()) * (1 / g));
                            newLhs += carl::floor( (lhs().constantPart() / g) ) + ONE_RATIONAL;
                            return new Constraint( newLhs, Relation::LEQ );
                        }
                        case Relation::GEQ:
                        {
                            Polynomial newLhs = ((lhs() - lhs().constantPart()) * (1 / g));
                            newLhs += carl::floor( (lhs().constantPart() / g) );
                            return new Constraint( newLhs, Relation::GEQ );
                        }
                        case Relation::LESS:
                        {
                            Polynomial newLhs = ((lhs() - lhs().constantPart()) * (1 / g));
                            newLhs += carl::floor( (lhs().constantPart() / g) ) + ONE_RATIONAL;
                            return new Constraint( newLhs, Relation::LEQ );
                        }
                        case Relation::GREATER:
                        {
                            Polynomial newLhs = ((lhs() - lhs().constantPart()) * (1 / g));
                            newLhs += carl::floor( (lhs().constantPart() / g) );
                            return new Constraint( newLhs, Relation::GEQ );
                        }
                        default:
                            assert( false );
                    }
                }
            }
        }
        return nullptr;
    }

    void Constraint::init()
    {
        if( hasIntegerValuedVariable() && !hasRealValuedVariable() )
        {
            if( relation() == Relation::LESS )
            {
                mLhs = mLhs + ONE_RATIONAL;
                mRelation = Relation::LEQ;
                mHash = CONSTRAINT_HASH( mLhs, mRelation );
            }
            if( relation() == Relation::GREATER )
            {
                mLhs = mLhs - ONE_RATIONAL;
                mRelation = Relation::GEQ;
                mHash = CONSTRAINT_HASH( mLhs, mRelation );
            }
        }
        carl::VariablesInformation<false,Polynomial> varinfos = mLhs.getVarInfo<false>();
        for( auto varInfo = varinfos.begin(); varInfo != varinfos.end(); ++varInfo )
            mVarInfoMap.emplace_hint( mVarInfoMap.end(), *varInfo );
        mLhsDefinitess = mLhs.definiteness();
    }
    
    void Constraint::initFactorization() const 
    {
        #ifdef SMTRAT_STRAT_Factorization
        #ifdef USE_GINAC
        if( lhs().nrTerms() <= MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION && mVariables.size() <= MAX_DIMENSION_FOR_FACTORIZATION
            && maxDegree() <= MAX_DEGREE_FOR_FACTORIZATION && maxDegree() >= MIN_DEGREE_FOR_FACTORIZATION )
        {
            mFactorization = ginacFactorization( mLhs );
        }
        #else
        mFactorization.insert( pair<Polynomial, unsigned>( mLhs, 1 ) );
        #endif
        #else
        mFactorization.insert( pair<Polynomial, unsigned>( mLhs, 1 ) );
        #endif
    }

    bool Constraint::operator<( const Constraint& _constraint ) const
    {
        assert( mID > 0 && _constraint.id() > 0 );
        return mID < _constraint.id();
    }

    bool Constraint::operator==( const Constraint& _constraint ) const
    {
        if( mID == 0 || _constraint.id() == 0 )
        {
            return relation() == _constraint.relation() && lhs() == _constraint.lhs();
        }
        return mID == _constraint.id();
    }

    ostream& operator<<( ostream& _out, const Constraint& _constraint )
    {
        _out << _constraint.toString();
        return _out;
    }

    string Constraint::toString( unsigned _unequalSwitch, bool _infix, bool _friendlyVarNames ) const
    {
        string result = "";
        if( _infix )
            result = mLhs.toString( true, _friendlyVarNames );
        else
            result += "(";
        switch( relation() )
        {
            case Relation::EQ:
                result += "=";
                break;
            case Relation::NEQ:
                if( _infix )
                {
                    if( _unequalSwitch == 1 )
                        result += "<>";
                    else if( _unequalSwitch == 2 )
                        result += "/=";
                    else // standard case
                        result += "!=";
                }
                else
                {
                    if( _unequalSwitch == 0 ) // standard case
                        result += "!=";
                    else if( _unequalSwitch == 1 )
                    {
                        string lhsString = mLhs.toString( false, _friendlyVarNames );
                        return "(or (< " + lhsString + " 0) (> " + lhsString + " 0))";
                    }
                    else
                    {
                        string lhsString = mLhs.toString( false, _friendlyVarNames );
                        return "(not (= " + lhsString + " 0))";
                    }
                }
                break;
            case Relation::LESS:
                result += "<";
                break;
            case Relation::GREATER:
                result += ">";
                break;
            case Relation::LEQ:
                result += "<=";
                break;
            case Relation::GEQ:
                result += ">=";
                break;
            default:
                result += "~";
        }
        result += (_infix ? "0" : (" " + mLhs.toString( false, _friendlyVarNames ) + " 0)"));
        return result;
    }

    void Constraint::printProperties( ostream& _out ) const
    {
        _out << "Properties:" << endl;
        _out << "   Definitess:              ";
        switch( mLhsDefinitess )
        {
            case Definiteness::NON:
                _out << "NON" << endl;
                break;
            case Definiteness::POSITIVE:
                _out << "POSITIVE" << endl;
                break;
            case Definiteness::POSITIVE_SEMI:
                _out << "POSITIVE_SEMI" << endl;
                break;
            case Definiteness::NEGATIVE:
                _out << "NEGATIVE" << endl;
                break;
            case Definiteness::NEGATIVE_SEMI:
                _out << "NEGATIVE_SEMI" << endl;
                break;
            default:
                _out << "UNDEFINED" << endl;
                break;
        }
        _out << "   The number of monomials: " << mLhs.nrTerms() << endl;
        _out << "   The maximal degree:      " << (mLhs.isZero() ? 0 : mLhs.totalDegree()) << endl;
        _out << "   The constant part:       " << constantPart() << endl;
        _out << "   Variables:" << endl;
        for( auto vi = mVarInfoMap.begin(); vi != mVarInfoMap.end(); ++vi )
        {
            _out << "        " << vi->first << " has " << vi->second.occurence() << " occurences." << endl;
            _out << "        " << vi->first << " has the maximal degree of " << vi->second.maxDegree() << "." << endl;
            _out << "        " << vi->first << " has the minimal degree of " << vi->second.minDegree() << "." << endl;
        }
    }
    
    std::string Constraint::relationToString( const Relation _rel )
    {
        switch( _rel )
        {
            case Relation::EQ:
                return "=";
            case Relation::NEQ:
                return "!=";
            case Relation::LEQ:
                return "<=";
            case Relation::GEQ:
                return ">=";
            case Relation::LESS:
                return "<";
            case Relation::GREATER:
                return ">";
            default:
                return "~";
        }
    }
    
    bool Constraint::evaluate( const Rational& _value, Relation _relation )
    {
        switch( _relation )
        {
            case Relation::EQ:
            {
                if( _value == 0 ) return true;
                else return false;
            }
            case Relation::NEQ:
            {
                if( _value == 0 ) return false;
                else return true;
            }
            case Relation::LESS:
            {
                if( _value < 0 ) return true;
                else return false;
            }
            case Relation::GREATER:
            {
                if( _value > 0 ) return true;
                else return false;
            }
            case Relation::LEQ:
            {
                if( _value <= 0 ) return true;
                else return false;
            }
            case Relation::GEQ:
            {
                if( _value >= 0 ) return true;
                else return false;
            }
            default:
            {
                cout << "Error in isConsistent: unexpected relation symbol." << endl;
                return false;
            }
        }
    }
    
    Relation Constraint::invertRelation( const Relation _rel )
    {
        switch( _rel )
        {
            case Relation::EQ:
                return Relation::NEQ;
            case Relation::NEQ:
                return Relation::EQ;
            case Relation::LEQ:
                return Relation::GREATER;
            case Relation::GEQ:
                return Relation::LESS;
            case Relation::LESS:
                return Relation::GEQ;
            case Relation::GREATER:
                return Relation::LEQ;
            default:
                assert( false );
                return Relation::EQ;
        }
    }
    
    Relation Constraint::turnAroundRelation( const Relation _rel )
    {
        switch( _rel )
        {
            case Relation::EQ:
                return Relation::EQ;
            case Relation::NEQ:
                return Relation::NEQ;
            case Relation::LEQ:
                return Relation::GEQ;
            case Relation::GEQ:
                return Relation::LEQ;
            case Relation::LESS:
                return Relation::GREATER;
            case Relation::GREATER:
                return Relation::LESS;
            default:
                assert( false );
                return Relation::EQ;
        }
    }
    
    static const signed A_IFF_B = 2;
    static const signed A_IMPLIES_B = 1;
    static const signed B_IMPLIES_A = -1;
    static const signed NOT__A_AND_B = -2;
    static const signed A_AND_B__IFF_C = -3;
    static const signed A_XOR_B = -4;

    signed Constraint::compare( const Constraint* _constraintA, const Constraint* _constraintB )
    {
        /*
         * Check whether it holds that 
         * 
         *                      _constraintA  =  a_1*m_1+...+a_k*m_k + c ~ 0
         * and 
         *                      _constraintB  =  b_1*m_1+...+b_k*m_k + d ~ 0, 
         * 
         * where a_1,..., a_k, b_1,..., b_k, c, d are rational coefficients, 
         *       m_1,..., m_k are non-constant monomials and 
         *       exists a rational g such that 
         * 
         *                   a_i = g * b_i for all 1<=i<=k 
         *              or   b_i = g * a_i for all 1<=i<=k 
         */
        auto termA = _constraintA->lhs().rbegin();
        auto termB = _constraintB->lhs().rbegin();
        Rational g = 1;
        Rational c = 0;
        Rational d = 0;
        bool termACoeffGreater = false;
        bool termBCoeffGreater = false;
        // The first two terms are not constant.
        if( termA != _constraintA->lhs().rend() && !(*termA)->isConstant() && termB != _constraintB->lhs().rend() && !(*termB)->isConstant() )
        {
            if( *(*termA)->monomial() != *(*termB)->monomial() ) return 0;
            // Find an appropriate g.
            Rational termAcoeffAbs = cln::abs( (*termA)->coeff() ); // TODO: use some method of carl instead of cln::abs
            Rational termBcoeffAbs = cln::abs( (*termB)->coeff() );
            termACoeffGreater = termAcoeffAbs > termBcoeffAbs; 
            termBCoeffGreater = termAcoeffAbs < termBcoeffAbs;
            if( termACoeffGreater ) 
                g = (*termA)->coeff()/(*termB)->coeff();
            else if( termBCoeffGreater ) 
                g = (*termB)->coeff()/(*termA)->coeff();
            else if( (*termA)->coeff() == (*termB)->coeff() ) 
                g = Rational( 1 );
            else
            {
                g = Rational( -1 );
                termBCoeffGreater = true;
            }
            // Check whether the left-hand sides of the two constraints without their constant part
            // are equal when one of the left-hand sides is multiplied by g.
            ++termA;
            ++termB;
            while( termA != _constraintA->lhs().rend() && !(*termA)->isConstant() && termB != _constraintB->lhs().rend() && !(*termB)->isConstant() )
            {
                if( *(*termA)->monomial() != *(*termB)->monomial() ) return 0;
                else if( termACoeffGreater )
                {
                    if( (*termA)->coeff() != g * (*termB)->coeff() ) return 0;
                }
                else if( termBCoeffGreater )
                {
                    if( g * (*termA)->coeff() != (*termB)->coeff() ) return 0;
                }
                else if( (*termA)->coeff() != (*termB)->coeff() ) return 0;
                ++termA;
                ++termB;
            }
        }
        if( termA != _constraintA->lhs().rend() )
        {
            if( (*termA)->isConstant() )
            {
                c = (termBCoeffGreater ? (*termA)->coeff() * g : (*termA)->coeff());
            }
            else
                return 0;
        }
        if( termB != _constraintB->lhs().rend() )
        {
            if( (*termB)->isConstant() )
            {
                d = (termACoeffGreater ? (*termB)->coeff() * g : (*termB)->coeff());
            }
            else
                return 0;
        }
        // Apply the multiplication by a negative g to the according relation symbol, which
        // has to be turned around then.
        Relation relA = _constraintA->relation();
        Relation relB = _constraintB->relation();
        if( g < 0 )
        {
            switch( (termACoeffGreater ? relB : relA ) )
            {
                case Relation::LEQ:
                    if( termACoeffGreater ) relB = Relation::GEQ; 
                    else relA = Relation::GEQ;
                    break;
                case Relation::GEQ:
                    if( termACoeffGreater ) relB = Relation::LEQ; 
                    else relA = Relation::LEQ;
                    break;
                case Relation::LESS:
                    if( termACoeffGreater ) relB = Relation::GREATER;
                    else relA = Relation::GREATER;
                    break;
                case Relation::GREATER:
                    if( termACoeffGreater )  relB = Relation::LESS;
                    else relA = Relation::LESS;
                    break;
                default:
                    break;
            }
        }
        // Compare the adapted constant parts.
        switch( relB )
        {
            case Relation::EQ:
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d=0
                        if( c == d ) return A_IFF_B; 
                        else return NOT__A_AND_B;
                    case Relation::NEQ: // p+c!=0  and  p+d=0
                        if( c == d ) return A_XOR_B;
                        else return B_IMPLIES_A;
                    case Relation::LESS: // p+c<0  and  p+d=0
                        if( c < d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case Relation::GREATER: // p+c>0  and  p+d=0
                        if( c > d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case Relation::LEQ: // p+c<=0  and  p+d=0
                        if( c <= d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    case Relation::GEQ: // p+c>=0  and  p+d=0
                        if( c >= d ) return B_IMPLIES_A;
                        else return NOT__A_AND_B;
                    default:
                        return false;
                }
            case Relation::NEQ:
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d!=0
                        if( c == d ) return A_XOR_B;
                        else return A_IMPLIES_B;
                    case Relation::NEQ: // p+c!=0  and  p+d!=0
                        if( c == d ) return A_IFF_B;
                        else return 0;
                    case Relation::LESS: // p+c<0  and  p+d!=0
                        if( c >= d ) return A_IMPLIES_B;
                        else return 0;
                    case Relation::GREATER: // p+c>0  and  p+d!=0
                        if( c <= d ) return A_IMPLIES_B;
                        else return 0;
                    case Relation::LEQ: // p+c<=0  and  p+d!=0
                        if( c > d ) return A_IMPLIES_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case Relation::GEQ: // p+c>=0  and  p+d!=0
                        if( c < d ) return A_IMPLIES_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    default:
                        return 0;
                }
            case Relation::LESS:
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d<0
                        if( c > d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case Relation::NEQ: // p+c!=0  and  p+d<0
                        if( c <= d ) return B_IMPLIES_A;
                        else return 0;
                    case Relation::LESS: // p+c<0  and  p+d<0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case Relation::GREATER: // p+c>0  and  p+d<0
                        if( c <= d ) return NOT__A_AND_B;
                        else return 0;
                    case Relation::LEQ: // p+c<=0  and  p+d<0
                        if( c > d ) return A_IMPLIES_B;
                        else return B_IMPLIES_A;
                    case Relation::GEQ: // p+c>=0  and  p+d<0
                        if( c < d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    default:
                        return 0;
                }
            case Relation::GREATER:
            {
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d>0
                        if( c < d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case Relation::NEQ: // p+c!=0  and  p+d>0
                        if( c >= d ) return B_IMPLIES_A;
                        else return 0;
                    case Relation::LESS: // p+c<0  and  p+d>0
                        if( c >= d ) return NOT__A_AND_B;
                        else return 0;
                    case Relation::GREATER: // p+c>0  and  p+d>0
                        if( c == d ) return A_IFF_B;
                        else if( c > d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case Relation::LEQ: // p+c<=0  and  p+d>0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case Relation::GEQ: // p+c>=0  and  p+d>0
                        if( c > d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    default:
                        return 0;
                }
            }
            case Relation::LEQ:
            {
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d<=0
                        if( c >= d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case Relation::NEQ: // p+c!=0  and  p+d<=0
                        if( c < d ) return B_IMPLIES_A;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case Relation::LESS: // p+c<0  and  p+d<=0
                        if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case Relation::GREATER: // p+c>0  and  p+d<=0
                        if( c < d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case Relation::LEQ: // p+c<=0  and  p+d<=0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case Relation::GEQ: // p+c>=0  and  p+d<=0
                        if( c < d ) return NOT__A_AND_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    default:
                        return 0;
                }
            }
            case Relation::GEQ:
            {
                switch( relA )
                {
                    case Relation::EQ: // p+c=0  and  p+d>=0
                        if( c <= d ) return A_IMPLIES_B;
                        else return NOT__A_AND_B;
                    case Relation::NEQ: // p+c!=0  and  p+d>=0
                        if( c > d ) return B_IMPLIES_A;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case Relation::LESS: // p+c<0  and  p+d>=0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_XOR_B;
                        else return 0;
                    case Relation::GREATER: // p+c>0  and  p+d>=0
                        if( c < d ) return B_IMPLIES_A;
                        else return A_IMPLIES_B;
                    case Relation::LEQ: // p+c<=0  and  p+d>=0
                        if( c > d ) return NOT__A_AND_B;
                        else if( c == d ) return A_AND_B__IFF_C;
                        else return 0;
                    case Relation::GEQ: // p+c>=0  and  p+d>=0
                        if( c == d ) return A_IFF_B;
                        else if( c < d ) return A_IMPLIES_B;
                        else return B_IMPLIES_A;
                    default:
                        return 0;
                }
            }
            default:
                return 0;
        }
    }
}    // namespace smtrat

