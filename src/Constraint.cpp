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
 * Class to create a constraint object.
 * @author Florian Corzilius
 * @since 2010-04-26
 * @version 2011-12-05
 */

//#define VS_DEBUG

#include "Constraint.h"

namespace smtrat
{
    using namespace std;
    using namespace GiNaC;

    /**
     * Constructors:
     */
    Constraint::Constraint()
    {
        pLhs              = new ex( 0 );
        rLhs()            = rLhs();
        pMultiRootLessLhs = NULL;
        mRelation         = CR_EQ;
        mVariables        = symtab();
    }

    Constraint::Constraint( const GiNaC::ex& _lhs, const Constraint_Relation _cr, const symtab& _vars )
    {
        pLhs              = new ex( _lhs );
        rLhs()            = rLhs();
        pMultiRootLessLhs = NULL;
        mRelation         = Constraint_Relation( _cr );
        mVariables        = symtab();
        for( symtab::const_iterator var = _vars.begin(); var != _vars.end(); ++var )
        {
            if( pLhs->has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        #ifdef TS_CONSTRAINT_SIMPLIFIER
        simplify();
        #endif
    }

    Constraint::Constraint( const GiNaC::ex& _lhs, const GiNaC::ex& _rhs, const Constraint_Relation& _cr, const symtab& _vars )
    {
        pLhs              = new ex( _lhs - _rhs );
        rLhs()            = rLhs();
        pMultiRootLessLhs = NULL;
        mRelation         = Constraint_Relation( _cr );
        mVariables        = symtab();
        for( symtab::const_iterator var = _vars.begin(); var != _vars.end(); ++var )
        {
            if( pLhs->has( var->second ) )
            {
                mVariables.insert( *var );
            }
        }
        #ifdef TS_CONSTRAINT_SIMPLIFIER
        simplify();
        #endif
    }

    Constraint::Constraint( const Constraint& _constraint )
    {
        pLhs              = new ex( _constraint.lhs() );
        pMultiRootLessLhs = NULL;
        mRelation         = Constraint_Relation( _constraint.relation() );
        mVariables        = symtab( _constraint.variables() );
    }

    /**
     * Destructor:
     */
    Constraint::~Constraint()
    {
        delete pLhs;
        delete pMultiRootLessLhs;
    }

    /**
     * Methods:
     */

    /**
     * @param _variableName The name of the variable we search for.
     * @param _variable     The according variable.
     *
     * @return true,    if the variable occurs in this constraint;
     *         false,   otherwise.
     */
    bool Constraint::variable( const string& _variableName, symbol& _variable ) const
    {
        symtab::const_iterator var = variables().find( _variableName );
        if( var != variables().end() )
        {
            _variable = ex_to<symbol>( var->second );
            return true;
        }
        else
        {
            return false;
        }
    }

    /**
     * Checks if the variable corresponding to the given variable name occurs in the constraint.
     *
     * @param _varName  The name of the variable.
     *
     * @return  true    , if the given variable occurs in the constraint;
     *          false   , otherwise.
     */
    bool Constraint::hasVariable( const std::string& _varName ) const
    {
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            if( var->first == _varName )
                return true;
        }
        return false;
    }

    /**
     * Checks, whether the constraint is consistent.
     * It differs between, containing variables, consistent, and inconsistent.
     *
     * @return 0, if the constraint is not consistent.
     *         1, if the constraint is consistent.
     *         2, if the constraint still contains variables.
     */
    unsigned Constraint::isConsistent() const
    {
        #ifdef VS_DEBUG
        cout << "   Try: ";
        print( cout );
        #endif
        unsigned result = 0;
        if( variables().size() == 0 )
        {
            switch( relation() )
            {
                case CR_EQ:
                {
                    if( lhs() == 0 )
                        result = 1;
                    break;
                }
                case CR_NEQ:
                {
                    if( lhs() != 0 )
                        result = 1;
                    break;
                }
                case CR_LESS:
                {
                    if( lhs() < 0 )
                        result = 1;
                    break;
                }
                case CR_GREATER:
                {
                    if( lhs() > 0 )
                        result = 1;
                    break;
                }
                case CR_LEQ:
                {
                    if( lhs() <= 0 )
                        result = 1;
                    break;
                }
                case CR_GEQ:
                {
                    if( lhs() >= 0 )
                        result = 1;
                    break;
                }
                default:
                    cout << "Error in isConsistent: unexpected relation symbol." << endl;
            }
        }
        else
            result = 2;
        #ifdef VS_DEBUG
        cout << " -> " << result << endl;
        #endif
        return result;
    }

    /**
     * Valuates the constraint according to a variable (it possibly not contains).
     *
     *      +++ Note: An equation must always be better than constraints with
     *      +++       other relation symbols.
     *
     * @param _consideredVariable The variable which is considered in this valuation.
     *
     * @return A valuation of the constraint according to an heuristic.
     */
    unsigned Constraint::valuate( const string _consideredVariable, const unsigned _maxNumberOfVars, const bool _forElimination )
    {
        symtab::const_iterator var = variables().find( _consideredVariable );
        if( var != variables().end() )
        {
            /*
             * Round the maximal number of variables.
             */
            unsigned roundedMaxNumberOfVars = 1;
            while( roundedMaxNumberOfVars <= _maxNumberOfVars )
            {
                roundedMaxNumberOfVars *= 10;
            }

            vector<ex> coeffs = vector<ex>();
            if( _forElimination )
            {
                for( int i = 0; i <= multiRootLessLhs( ex_to<symbol>( var->second ) ).degree( ex( var->second ) ); ++i )
                {
                    coeffs.push_back( ex( multiRootLessLhs( ex_to<symbol>( var->second ) ).coeff( ex( var->second ), i ) ) );
                }
            }
            else
            {
                getCoefficients( ex_to<symbol>( var->second ), coeffs );
            }

            /*
             * Check the relation symbol.
             */
            unsigned relationSymbolWeight = 0;
            switch( relation() )
            {
                case CR_EQ:
                    relationSymbolWeight += 4;
                    break;
                case CR_GEQ:
                    relationSymbolWeight += 3;
                    break;
                case CR_LEQ:
                    relationSymbolWeight += 3;
                    break;
                case CR_LESS:
                    relationSymbolWeight += 2;
                    break;
                case CR_GREATER:
                    relationSymbolWeight += 2;
                    break;
                case CR_NEQ:
                    relationSymbolWeight += 1;
                    break;
                default:
                    return 0;
            }

            /*
             * Check the degree of the variable.
             */
            unsigned degree = coeffs.size() - 1;

            /*
             * Check the leading coefficient of the  given variable.
             */
            unsigned lCoeffWeight = 0;

            if( degree <= 1 )
            {
                if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 3;
                }
                else
                {
                    lCoeffWeight += 1;
                }
            }
            else if( degree == 2 )
            {
                if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) && coeffs.at( coeffs.size() - 2 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 3;
                }
                else if( coeffs.at( coeffs.size() - 1 ).info( info_flags::rational ) )
                {
                    lCoeffWeight += 2;
                }
                else
                {
                    lCoeffWeight += 1;
                }
            }

            /*
             * Check the number of variables.
             */
            unsigned numberOfVariableWeight = roundedMaxNumberOfVars - variables().size();

            unsigned result;
            if( degree <= 2 )
            {
                if( variables().size() == 1 )
                {
                    result = 100 * roundedMaxNumberOfVars * relationSymbolWeight + 10 * roundedMaxNumberOfVars * lCoeffWeight
                             + 3 * roundedMaxNumberOfVars * (3 - degree);
                }
                else
                {
                    result = 100 * roundedMaxNumberOfVars * relationSymbolWeight + 10 * roundedMaxNumberOfVars * lCoeffWeight
                             + roundedMaxNumberOfVars * (3 - degree) + numberOfVariableWeight;
                }
            }
            else
            {
                result = 10 * roundedMaxNumberOfVars * relationSymbolWeight + roundedMaxNumberOfVars * lCoeffWeight + numberOfVariableWeight;
            }
            return result;
        }
        else
        {
            return 0;
        }
    }

    /**
     * Finds the most adequate variable in the constraint according to an heuristics.
     *
     * @return true     ,if the constraint has any variable;
     *         false    ,otherwise.
     */
    bool Constraint::bestVariable( std::string& _bestVariable ) const
    {
        symtab::const_iterator var = variables().begin();
        if( var == variables().end() )
        {
            return false;
        }
        symtab::const_iterator bestVar = var;
        var++;
        while( var != variables().end() )
        {
            if( lhs().degree( ex( bestVar->second ) ) > lhs().degree( ex( var->second ) ) )
            {
                bestVar = var;
            }
            var++;
        }
        _bestVariable = bestVar->first;
        return true;
    }

    /**
     * Valuates the constraint according to a variable (it possibly not contains).
     *
     * @param _bestVariable The best variable according to some constraints.
     *
     * @return A valuation of the constraint according to an heuristic.
     */
    unsigned Constraint::bestVariable2( std::string& _bestVariable ) const
    {
        /*
         * If the constraint has no variables, return 0.
         */
        symtab::const_iterator var = variables().begin();
        if( var == variables().end() )
        {
            return 0;
        }

        /*
         * Check whether the leading coefficient of the currently considered variable (in this
         * constraint) is constant.
         */
        symtab::const_iterator bestVar                                   = var;
        bool                   bestVariableLeadingCoefficientHasVariable = false;
        for( symtab::const_iterator var2 = variables().begin(); var2 != variables().end(); ++var2 )
        {
            if( lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
            {
                bestVariableLeadingCoefficientHasVariable = true;
                break;
            }
        }
        var++;
        while( var != variables().end() )
        {
            /*
             * Choose the variable with the smaller degree.
             */
            if( lhs().degree( ex( bestVar->second ) ) > lhs().degree( ex( var->second ) ) )
            {
                bestVar = var;

                /*
                 * Check whether the leading coefficient of the currently considered variable (in this
                 * constraint) is constant.
                 */
                bestVariableLeadingCoefficientHasVariable = false;
                for( symtab::const_iterator var2 = variables().begin(); var2 != variables().end(); ++var2 )
                {
                    if( lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
                    {
                        bestVariableLeadingCoefficientHasVariable = true;
                        break;
                    }
                }
            }

            /*
             * If the degrees are equal, choose the variable whose leading coefficient is constant.
             * If both are not constant or both are constant, take the first variable (alphabetically
             * order)
             */
            else if( bestVariableLeadingCoefficientHasVariable && lhs().degree( bestVar->second ) == lhs().degree( ex( var->second ) ) )
            {
                symtab::const_iterator var2 = variables().begin();
                while( var2 != variables().end() )
                {
                    if( lhs().lcoeff( ex( var->second ) ).has( ex( var2->second ) ) )
                    {
                        break;
                    }
                    var2++;
                }
                if( var2 == variables().end() )
                {
                    bestVar                                   = var;
                    bestVariableLeadingCoefficientHasVariable = false;
                }
            }
            var++;
        }

        /**
         * Determine the quality: The most influence has the relation symbol, than the degree,
         * than the fact, that the variable has a constant leading coefficient.
         */
        unsigned variableQuality = 0;
        unsigned degree          = static_cast<unsigned>(lhs().degree( ex( bestVar->second ) ));
        if( relation() == CR_EQ )
        {
            variableQuality = 1000 * degree;
            if( !bestVariableLeadingCoefficientHasVariable )
            {
                variableQuality++;
            }
        }
        else
        {
            if( relation() == CR_GEQ || relation() == CR_LEQ )
            {
                variableQuality = 100 * degree;
                if( !bestVariableLeadingCoefficientHasVariable )
                {
                    variableQuality++;
                }
            }
            else
            {
                variableQuality = 10 * degree;
                if( !bestVariableLeadingCoefficientHasVariable )
                {
                    variableQuality++;
                }
            }
        }
        _bestVariable = bestVar->first;
        return variableQuality;
    }

    /**
     * Checks whether the constraints solutions for the given variable are finitely many (at least one).
     *
     * @param _variableName The variable for which the method detects, whether it is linear.
     *
     * @return  true,   if the constraints solutions for the given variable are finitely many (at least one);
     *          false,  otherwise.
     */
    bool Constraint::hasFinitelyManySolutionsIn( const std::string& _variableName ) const
    {
        if( relation() != CR_EQ )
        {
            return false;
        }
        else
        {
            symtab::const_iterator var = variables().find( _variableName );
            if( var != variables().end() )
            {
                vector<ex> coeffs = vector<ex>();
                getCoefficients( ex_to<symbol>( var->second ), coeffs );
                signed i = coeffs.size() - 1;

                for( ; i > 0; --i )
                {
                    if( !coeffs.at( i ).info( info_flags::rational ) )
                    {
                        return false;
                    }
                }
                return true;
            }
            else
            {
                return false;
            }
        }
    }

    /**
     * Calculates the coefficients of the given variable in this constraint.
     *
     * @param _variable         The variable of which you want to find the coefficients.
     * @param _coefficients     A vector of the coefficients corresponding the given variable.
     *                      The ith entry of the vector contains the coefficient of the ith
     *                      power of the variable.
     */
    void Constraint::getCoefficients( const symbol& _variable, vector<GiNaC::ex>& _coefficients ) const
    {
        for( int i = 0; i <= lhs().degree( ex( _variable ) ); ++i )
        {
            _coefficients.push_back( ex( lhs().expand().coeff( ex( _variable ), i ) ) );
        }
    }

    /**
     * Determines the degree of the variable in this constraint.
     *
     * @param _variableName The name of the variable of which you want to have the degree.
     */
    signed Constraint::degree( const std::string& _variableName ) const
    {
        symbol sym;
        if( variable( _variableName, sym ) )
        {
            return lhs().degree( ex( sym ) );
        }
        else
        {
            return 0;
        }
    }

    /**
     * Determines the highest degree of all variables in this constraint.
     */
    signed Constraint::highestDegree() const
    {
        signed result = 0;
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            signed d = lhs().degree( ex( var->second ) );
            if( d > result )
                result = d;
        }
        return result;
    }

    /**
     * Checks whether the constraint is linear in all variables.
     */
    bool Constraint::isLinear() const
    {
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            if( lhs().degree( ex( var->second ) ) > 1 )
            {
                return false;
            }
        }
        return true;
    }

    /**
     * Gets the linear coefficients of each variable and their common constant part.
     *
     * @return The linear coefficients of each variable and their common constant part.
     */
    vector<ex> Constraint::linearAndConstantCoefficients() const
    {
        vector<ex> result = vector<ex>();
        ex constantPart = lhs();
        for( symtab::const_iterator var = variables().begin(); var != variables().end(); ++var )
        {
            result.push_back( ex( constantPart.expand().coeff( ex( var->second ), 1 ) ) );
            constantPart = ex( constantPart.coeff( ex( var->second ), 0 ) );
        }
        result.push_back( constantPart );
        return result;
    }

    /**
     * Compares whether the two expressions are the same.
     *
     * @param _expressionA
     * @param _varsA
     * @param _expressionB
     * @param _varsB
     *
     * @return  -1, if the first expression is smaller than the second according to this order.
     *          0, if the first expression is equal to the second according to this order.
     *          1, if the first expression is greater than the second according to this order.
     */
    int Constraint::exCompare( const GiNaC::ex& _expressionA, const symtab& _varsA, const GiNaC::ex& _expressionB, const symtab& _varsB )
    {
        symtab::const_iterator varA = _varsA.begin();
        symtab::const_iterator varB = _varsB.begin();
        if( varA != _varsA.end() && varB != _varsB.end() )
        {
            int cmpValue = varA->first.compare( varB->first );
            if( cmpValue < 0 )
            {
                return -1;
            }
            else if( cmpValue > 0 )
            {
                return 1;
            }
            else
            {
                ex currentVar = ex( varA->second );
                signed degreeA = _expressionA.degree( currentVar );
                signed degreeB = _expressionB.degree( currentVar );
                if( degreeA < degreeB )
                {
                    return -1;
                }
                else if( degreeA > degreeB )
                {
                    return 1;
                }
                else
                {
                    varA++;
                    varB++;
                    for( int i = 0; i <= degreeA; ++i )
                    {
                        symtab remVarsA = symtab( varA, _varsA.end() );
                        ex ithCoeffA    = _expressionA.coeff( currentVar, i );
                        symtab::iterator var = remVarsA.begin();
                        while( var != remVarsA.end() )
                        {
                            if( !ithCoeffA.has( ex( var->second ) ) )
                            {
                                remVarsA.erase( var++ );
                            }
                            else
                            {
                                var++;
                            }
                        }
                        symtab remVarsB = symtab( varB, _varsB.end() );
                        ex ithCoeffB    = _expressionB.coeff( currentVar, i );
                        var             = remVarsB.begin();
                        while( var != remVarsB.end() )
                        {
                            if( !ithCoeffB.has( ex( var->second ) ) )
                            {
                                remVarsB.erase( var++ );
                            }
                            else
                            {
                                var++;
                            }
                        }
                        int coeffCompResult = exCompare( ithCoeffA, remVarsA, ithCoeffB, remVarsB );
                        if( coeffCompResult < 0 )
                        {
                            return -1;
                        }
                        else if( coeffCompResult > 0 )
                        {
                            return 1;
                        }
                    }
                    return 0;
                }
            }
        }
        else if( varB != _varsB.end() )
        {
            return -1;
        }
        else if( varA != _varsA.end() )
        {
            return 1;
        }
        else
        {
            if( _expressionA < _expressionB )
            {
                return -1;
            }
            else if( _expressionA > _expressionB )
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
    }

    ex& Constraint::multiRootLessLhs( const symbol& _variable )
    {
        /*
                if( pMultiRootLessLhs != NULL )
                {
                    if( pMultiRootLessLhs->first == ex( _variable ) )
                    {
                        return pMultiRootLessLhs->second;
                    }
                    else
                    {
                        pMultiRootLessLhs->first = ex( _variable );
                    }
                }

                ex derivate            = lhs().diff( _variable, 1 );
                ex gcdOfLhsAndDerivate = gcd( lhs(), derivate );
                gcdOfLhsAndDerivate    = gcdOfLhsAndDerivate.expand().normal();
                ex quotient;
                if( gcdOfLhsAndDerivate != 0 && divide( lhs(), gcdOfLhsAndDerivate, quotient ))
                {
                    if( pMultiRootLessLhs != NULL )
                    {
                        pMultiRootLessLhs->second = quotient;
                    }
                    else
                    {
                        pMultiRootLessLhs = new VS_MultiRootLessLhs( ex( _variable ), quotient );
                    }
                }
                else
                {
                    if( pMultiRootLessLhs != NULL )
                    {
                        pMultiRootLessLhs->second = lhs();
                    }
                    else
                    {
                        pMultiRootLessLhs = new VS_MultiRootLessLhs( ex( _variable ), lhs() );
                    }
                }
                return pMultiRootLessLhs->second;
        */
        return rLhs();
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is LEXOGRAPHICALLY smaller than the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator <( const Constraint& _constraint ) const
    {
        if( relation() < _constraint.relation() )
        {
            return true;
        }
        else if( relation() == _constraint.relation() )
        {
            if( exCompare( lhs(), variables(), _constraint.lhs(), _constraint.variables() ) == -1 )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  true,   if this constraint is equal to the given one;
     *          false,  otherwise.
     */
    bool Constraint::operator ==( const Constraint& _constraint ) const
    {
        if( relation() == _constraint.relation() )
        {
            if( lhs() == _constraint.lhs() )
            {
                return true;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }

    /**
     * Simplifies this constraint.
     */
    void Constraint::simplify()
    {
        if( !variables().empty() )
        {
            ex un, con, prim;
            lhs().unitcontprim( ex( variables().begin()->second ), un, con, prim );
            if( con.info( info_flags::rational ) )
            {
                rLhs() = prim * un;
            }
        }
    }

    /**
     * Gives the string represantion of the constraint.
     *
     * @return The string represantion of the constraint.
     */
    string Constraint::toString() const
    {
        string result = "";
        ostringstream sstream;
        sstream << lhs();
        result += sstream.str();
        switch( relation() )
        {
            case CR_EQ:
                result += "=";
                break;
            case CR_NEQ:
                result += "<>";
                break;
            case CR_LESS:
                result += "<";
                break;
            case CR_GREATER:
                result += ">";
                break;
            case CR_LEQ:
                result += "<=";
                break;
            case CR_GEQ:
                result += ">=";
                break;
            default:
                result += "~";
        }
        result += "0";
        return result;
    }

    /**
     * Prints the constraint representation to an output stream.
     *
     * @param _out The output stream to which the constraints representation is printed.
     */
    void Constraint::print( ostream& _out ) const
    {
        _out << lhs();
        switch( relation() )
        {
            case CR_EQ:
                _out << "=";
                break;
            case CR_NEQ:
                _out << "<>";
                break;
            case CR_LESS:
                _out << "<";
                break;
            case CR_GREATER:
                _out << ">";
                break;
            case CR_LEQ:
                _out << "<=";
                break;
            case CR_GEQ:
                _out << ">=";
                break;
            default:
                _out << "~";
        }
        _out << "0";
    }

    /**
     * Prints the constraint representation to an output stream.
     *
     * @param _out The output stream to which the constraints representation is printed.
     */
    void Constraint::print2( ostream& _out ) const
    {
        _out << lhs();
        switch( relation() )
        {
            case CR_EQ:
                _out << "=";
                break;
            case CR_NEQ:
                _out << "!=";
                break;
            case CR_LESS:
                _out << "<";
                break;
            case CR_GREATER:
                _out << ">";
                break;
            case CR_LEQ:
                _out << "<=";
                break;
            case CR_GEQ:
                _out << ">=";
                break;
            default:
                _out << "~";
        }
        _out << "0";
    }

    /**
     * Compares this constraint with the given constraint.
     *
     * @return  2,  if it is easy to decide that this constraint and the given constraint have the same solutions.(are equal)
     *          1,  if it is easy to decide that the given constraint includes all solutions of this constraint;
     *          -1, if it is easy to decide that this constraint includes all solutions if the given constraint;
     *          -2, if it is easy to decide that this constraint has no solution common with the given constraint;
     *          -3, if it is easy to decide that this constraint and the given constraint can be intersected;
     *          0,  otherwise.
     */
    signed Constraint::compare( const Constraint& _constraintA, const Constraint& _constraintB )
    {
        symtab::const_iterator var1 = _constraintA.variables().begin();
        symtab::const_iterator var2 = _constraintB.variables().begin();
        while( var1 != _constraintA.variables().end() && var2 != _constraintB.variables().end() )
        {
            if( strcmp( (*var1).first.c_str(), (*var2).first.c_str() ) == 0 )
            {
                var1++;
                var2++;
            }
            else
            {
                break;
            }
        }
        if( var1 == _constraintA.variables().end() && var2 == _constraintB.variables().end() )
        {
            ex lcoeffA = _constraintA.lhs().lcoeff( ex( _constraintA.variables().begin()->second ) );
            ex lcoeffB = _constraintB.lhs().lcoeff( ex( _constraintB.variables().begin()->second ) );
            ex lhsA    = _constraintA.lhs();
            ex lhsB    = _constraintB.lhs();
            if( lcoeffA.info( info_flags::rational ) && lcoeffB.info( info_flags::rational ) )
            {
                if( lcoeffB.info( info_flags::positive ) )
                {
                    lhsA = lhsA * lcoeffB;
                }
                else
                {
                    lhsA = lhsA * (-1) * lcoeffB;
                }
                if( lcoeffA.info( info_flags::positive ) )
                {
                    lhsB = lhsB * lcoeffA;
                }
                else
                {
                    lhsB = lhsB * (-1) * lcoeffA;
                }
            }
            else if( lcoeffA.info( info_flags::rational ) || lcoeffB.info( info_flags::rational ) )
            {
                return 0;
            }
            switch( _constraintB.relation() )
            {
                case CR_EQ:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::rational ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::rational ) )
                                return -2;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -2;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::rational ) )
                                return -1;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        default:
                            return false;
                    }
                }
                case CR_NEQ:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -2;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::rational ) )
                                return 1;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case CR_LESS:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case CR_GREATER:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -2;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::rational ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case CR_LEQ:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return -1;
                            if( result1.info( info_flags::positive ) )
                                return 1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -2;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            if( result2.info( info_flags::negative ) )
                                return 1;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                case CR_GEQ:
                {
                    switch( _constraintA.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = -1 * (lhsA - lhsB);
                            if( result1.info( info_flags::nonnegative ) )
                                return 1;
                            if( result1.info( info_flags::negative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            return 0;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::positive ) )
                                return -1;
                            return 0;
                        }
                        case CR_LESS:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::nonnegative ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2.info( info_flags::nonnegative ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            if( result1.info( info_flags::rational ) )
                                return 1;
                            ex result2 = -1 * (lhsA + lhsB);
                            if( result2.info( info_flags::nonnegative ) )
                                return -2;
                            return 0;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return -3;
                            if( result1.info( info_flags::positive ) )
                                return -2;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return 2;
                            if( result2.info( info_flags::positive ) )
                                return 1;
                            if( result2.info( info_flags::negative ) )
                                return -1;
                            return 0;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = lhsA - lhsB;
                            if( result1 == 0 )
                                return 2;
                            if( result1.info( info_flags::negative ) )
                                return 1;
                            if( result1.info( info_flags::positive ) )
                                return -1;
                            ex result2 = lhsA + lhsB;
                            if( result2 == 0 )
                                return -3;
                            if( result2.info( info_flags::negative ) )
                                return -2;
                            return 0;
                        }
                        default:
                            return 0;
                    }
                }
                default:
                    return 0;
            }
        }
        else
        {
            return 0;
        }
    }

    /**
     * Merges the two given constraints. The first constraint will be changed accordingly
     * if possible. (Assumption: This constraint OR the given constraint have to hold.)
     *
     * @param _constraintA  The first constraint to merge.
     * @param _constraintB  The second constraint to merge.
     *
     * @return  true,   if we can merge the two constraints to one constraint, e.g.
     *                  p<0 or p=0 -> p<=0;    p<0 or p>0 -> p!=0;   p<0 or p>=0 -> True ...
     *          false,  otherwise.
     */
    bool Constraint::mergeConstraints( Constraint& _constraintA, const Constraint& _constraintB )
    {
        symtab::const_iterator var1 = _constraintA.variables().begin();
        symtab::const_iterator var2 = _constraintB.variables().begin();
        while( var1 != _constraintA.variables().end() && var2 != _constraintB.variables().end() )
        {
            if( strcmp( var1->first.c_str(), var2->first.c_str() ) == 0 )
            {
                var1++;
                var2++;
            }
            else
            {
                break;
            }
        }
        if( var1 == _constraintA.variables().end() && var2 == _constraintB.variables().end() )
        {
            switch( _constraintA.relation() )
            {
                case CR_EQ:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            return false;
                        }
                        case CR_NEQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rLhs() = 0;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rLhs() = 0;
                                return true;
                            }
                            return false;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_LEQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_GEQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                case CR_NEQ:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rLhs() = 1;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rLhs() = 1;
                                return true;
                            }
                            return false;
                        }
                        case CR_NEQ:
                        {
                            return false;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                return true;
                            }
                            return false;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                return true;
                            }
                            return false;
                        }
                        case CR_LEQ:
                        {
                            return false;
                        }
                        case CR_GEQ:
                        {
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                case CR_LESS:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_LEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_NEQ:
                        {
                            return false;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA.lhs() + _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_NEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_NEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_LEQ:
                        {
                            return false;
                        }
                        case CR_GEQ:
                        {
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                case CR_GREATER:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                _constraintA.rRelation() = CR_GEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_NEQ:
                        {
                            return false;
                        }
                        case CR_LESS:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_NEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_GREATER:
                        {
                            ex result1 = _constraintA.lhs() + _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                _constraintA.rRelation() = CR_NEQ;
                                return true;
                            }
                            return false;
                        }
                        case CR_LEQ:
                        {
                            return false;
                        }
                        case CR_GEQ:
                        {
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                case CR_LEQ:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                return true;
                            }
                            return false;
                        }
                        case CR_NEQ:
                        {
                            return false;
                        }
                        case CR_LESS:
                        {
                            return false;
                        }
                        case CR_GREATER:
                        {
                            return false;
                        }
                        case CR_LEQ:
                        {
                            return false;
                        }
                        case CR_GEQ:
                        {
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                case CR_GEQ:
                {
                    switch( _constraintB.relation() )
                    {
                        case CR_EQ:
                        {
                            ex result1 = _constraintA.lhs() - _constraintB.lhs();
                            if( result1 == 0 )
                            {
                                return true;
                            }
                            ex result2 = _constraintA.lhs() + _constraintB.lhs();
                            if( result2 == 0 )
                            {
                                return true;
                            }
                            return false;
                        }
                        case CR_NEQ:
                        {
                            return false;
                        }
                        case CR_LESS:
                        {
                            return false;
                        }
                        case CR_GREATER:
                        {
                            return false;
                        }
                        case CR_LEQ:
                        {
                            return false;
                        }
                        case CR_GEQ:
                        {
                            return false;
                        }
                        default:
                            return false;
                    }
                }
                default:
                    return false;
            }
        }
        else
        {
            return false;
        }
    }

}    // namespace smtrat

