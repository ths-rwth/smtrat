/*
 * Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 * , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 *
 * OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso
 *
 * OpenSMT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * OpenSMT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
 */


#include "LRASolverA.h"
#include "LAVar.h"

using namespace GiNaC;
using namespace smtrat;
using namespace std;

namespace lra
{
    //
    // Constructor
    //
    LRASolverA::LRASolverA()
    {
        backtrack_points        = std::vector<size_t>();
        mExplanation            = std::vector<const smtrat::Constraint*>();
        explanationCoefficients = std::vector<GiNaC::numeric>();
        columns                 = VectorLAVar();
        rows                    = VectorLAVar();
        expressionLAVarMap      = ExpressionLAVarMap();
        expressionOriginMap     = ExpressionConstraintMap();

        // LRA-Solver Default configuration
        lra_poly_deduct_size = 0;
        lra_check_on_assert  = 0;

        checks_history       = std::vector<unsigned>();
        checks_history.push_back( 0 );

        first_update_after_backtrack = true;

        status                       = INIT;
        slack_vars                   = VectorLAVar();
        numbers_pool                 = std::vector<GiNaC::numeric*>();
        pushed_constraints           = std::vector<LAVarHistory>();
        touched_rows                 = std::set<LAVar*>();
    }

    //
    // Destructor
    //
    LRASolverA::~LRASolverA()
    {
        // Remove slack variables
        while( !columns.empty() )
        {
            LAVar* s = columns.back();
            columns.pop_back();
            assert( s );
            delete s;
        }
        // Remove numbers
        while( !numbers_pool.empty() )
        {
            assert( numbers_pool.back() );
            delete numbers_pool.back();
            numbers_pool.pop_back();
        }
    }

    //TODO: requires refactoring

    //
    // Reads the constraint into the solver
    //
    Answer LRASolverA::informA( const Constraint* const _constraint )
    {
        cout << "inform " << _constraint->toString() << endl;
        for( ExpressionConstraintMap::const_iterator iter = expressionOriginMap.begin(); iter != expressionOriginMap.end(); ++iter )
        {
            cout << iter->second->toString() << endl;
            if( *iter->second == *_constraint )
            {
                return Unknown;
            }
        }

        if( status != INIT )
        {
            // Treat the Enode as it is pushed on-the-fly
            //    status = INCREMENT;
            assert( status == SAT );
        }
        assert( _constraint->relation() == CR_LEQ || _constraint->relation() == CR_GEQ );    // TODO: Generalize it to arbitrary constraints, of course excluding NEQ.

        vector<ex> coefficients = _constraint->linearAndConstantCoefficients();
        numeric constantPart = ex_to<numeric>( coefficients.back() );

        bool revert = _constraint->relation() != CR_LEQ;

        /*
         * If the constraint compares only a single variable with a constant.
         */
        if( coefficients.size() == 1 )
        {
            return (_constraint->isConsistent() == 0 ? True : False);
        }
        else if( coefficients.size() == 2 )
        {
            assert( _constraint->variables().size() == 1 );

            if( ex_to<numeric>( coefficients.at( 0 ) ) < 0 )
            {
                revert = !revert;
            }

            numeric * bound;

            if( !numbers_pool.empty() )
            {
                bound = numbers_pool.back();
                numbers_pool.pop_back();
                *bound = numeric( ex_to<numeric>( coefficients.at( 1 ) ) / ex_to<numeric>( coefficients.at( 0 ) ) );
            }
            else
            {
                bound = new numeric( ex_to<numeric>( coefficients.at( 1 ) ) / ex_to<numeric>( coefficients.at( 0 ) ) );
            }

            ExpressionLAVarMap::iterator exToLAVar = expressionLAVarMap.find( ex( _constraint->variables().begin()->second ) );
            if( exToLAVar != expressionLAVarMap.end() )
            {
                exToLAVar->second->setBounds( _constraint->lhs(), *bound );
                expressionLAVarMap[_constraint->lhs()]  = exToLAVar->second;
                expressionOriginMap[_constraint->lhs()] = _constraint;
            }
            else
            {
                LAVar* x = new LAVar( _constraint->lhs(), ex( _constraint->variables().begin()->second ), *bound, revert );

                if( x->ID() >= static_cast<int>(columns.size()) )
                {
                    columns.resize( x->ID() + 1, NULL );
                }
                columns[x->ID()] = x;

                expressionLAVarMap.insert( pair<const ex, LAVar*>( ex( _constraint->variables().begin()->second ), x ) );
                //          expressionOriginMap.insert( pair< const ex, const Constraint* >( *_constraint->variables().begin()->second, _constraint ) );
                expressionLAVarMap[_constraint->lhs()]  = x;
                expressionOriginMap[_constraint->lhs()] = _constraint;
            }

            numbers_pool.push_back( bound );
        }
        else
        {
            ExpressionLAVarMap::iterator exToLAVar = expressionLAVarMap.find( ex( _constraint->variables().begin()->second ) );
            if( exToLAVar != expressionLAVarMap.end() )
            {
                exToLAVar->second->setBounds( _constraint->lhs(), ex_to<numeric>( coefficients.back() ) );
                expressionLAVarMap[_constraint->lhs()] = exToLAVar->second;
            }
            else
            {
                numeric * bound;
                if( !numbers_pool.empty() )
                {
                    bound = numbers_pool.back();
                    numbers_pool.pop_back();
                    *bound = numeric( ex_to<numeric>( coefficients.back() ) );
                }
                else
                {
                    bound = new numeric( ex_to<numeric>( coefficients.back() ) );
                }
                // introduce the slack variable with bounds on it
                LAVar* s = new LAVar( _constraint->lhs(), *bound, _constraint->lhs(), true );
                slack_vars.push_back( s );

                numbers_pool.push_back( bound );

                assert( s->basicID() != -1 );

                if( s->ID() >= static_cast<int>(columns.size()) )
                {
                    columns.resize( s->ID() + 1, NULL );
                }
                columns[s->ID()] = s;

                if( s->basicID() >= static_cast<int>(rows.size()) )
                {
                    rows.resize( s->basicID() + 1, NULL );
                }
                rows[s->basicID()] = s;

                if( !numbers_pool.empty() )
                {
                    bound = numbers_pool.back();
                    numbers_pool.pop_back();
                    *bound = numeric( -1 );
                }
                else
                {
                    bound = new numeric( -1 );
                }

                s->polynomial.add( s->ID(), 0, bound );

                expressionLAVarMap.insert( pair<const ex, LAVar*>( _constraint->lhs(), s ) );
                expressionOriginMap.insert( pair<const ex, const Constraint*>( _constraint->lhs(), _constraint ) );

                assert( coefficients.size() == _constraint->variables().size() + 1 );

                symtab::const_iterator var = _constraint->variables().begin();
                for( unsigned i = 0; i < coefficients.size() - 1; ++i )
                {
                    if( !numbers_pool.empty() )
                    {
                        bound = numbers_pool.back();
                        numbers_pool.pop_back();
                        *bound = numeric( ex_to<numeric>( coefficients.at( i ) ) );
                    }
                    else
                    {
                        bound = new numeric( ex_to<numeric>( coefficients.at( i ) ) );
                    }

                    ExpressionLAVarMap::iterator exToLAVar = expressionLAVarMap.find( ex( var->second ) );
                    if( exToLAVar != expressionLAVarMap.end() )
                    {
                        addVarToRow( s, exToLAVar->second, bound );
                    }
                    else
                    {
                        LAVar* x = new LAVar( ex( var->second ) );
                        slack_vars.push_back( x );
                        expressionLAVarMap.insert( pair<const ex, LAVar*>( ex( var->second ), x ) );
                        expressionOriginMap.insert( pair<const ex, const Constraint*>( ex( var->second ), _constraint ) );

                        if( x->ID() >= static_cast<int>(columns.size()) )
                        {
                            columns.resize( x->ID() + 1, NULL );
                        }
                        columns[x->ID()] = x;

                        x->binded_rows.add( s->basicID(), s->polynomial.add( x->ID(), x->binded_rows.free_pos(), bound ) );
                    }
                    ++var;
                    assert( s->basicID() != -1 );
                }
            }
        }
        print( cout );
        #if VERBOSE
        cout << "Informed of constraint " << _constraint->toString() << endl;
        //  cout << this << endl;
        #endif
        return Unknown;
    }

    //
    // Performs the main Check procedure to see if the current constraints and Tableau are satisfiable
    //
    bool LRASolverA::checkA()
    {
        cout << "check " << endl;
        //print( cout );
        //cout << endl << endl;
        // check if we stop reading constraints
        if( status == INIT )
        {
            initSolver();
        }

        LAVar*      x = NULL;

        VectorLAVar hist_x;
        VectorLAVar hist_y;
        bool        bland_rule    = false;
        unsigned    pivot_counter = 0;

        // keep doing pivotAndUpdate until the SAT/UNSAT status is confirmed
        while( 1 )
        {
            // clear the explanations vector
            mExplanation.clear();
            explanationCoefficients.clear();

            x = NULL;

            if( !bland_rule && (pivot_counter++ > columns.size()) )
            {
                //          cout << "pivot_counter exceeded: " << pivot_counter <<endl;
                bland_rule = true;
            }
            // look for the basic x with the smallest index which doesn't feat the bounds
            VectorLAVar::const_iterator it = rows.begin();
            for( ; it != rows.end(); ++it )
            {
                if( (*it)->isModelOutOfBounds() )
                {
                    if( bland_rule )
                    {
                        x = *it;
                        break;
                    }
                    else
                    {
                        if( x == NULL )
                        {
                            x = *it;
                            //                      tmp_d = x->overBound();
                        }
                        else if( x->polynomial.size() > (*it)->polynomial.size() )
                        //                  else if( tmp_d > ( *it )->overBound()  || tmp_d == ( *it )->overBound() && x->polynomial.size() > (*it)->polynomial.size())
                        //                  else if( x->polynomial.size() > (*it)->polynomial.size() || (x->polynomial.size() == (*it)->polynomial.size() && x->overBound() > ( *it )->overBound()) )
                        {
                            x = *it;
                            //                      tmp_d = x->overBound();
                        }
                    }
                }
            }

            if( x == NULL )
            {
                LAVar::saveModelGlobal();
                if( checks_history.back() < pushed_constraints.size() )
                {
                    checks_history.push_back( pushed_constraints.size() );
                }
                //          cout << "USUAL SAT" << endl;
                print( cout );
                cout << endl << __LINE__ << "SAT" << endl;
                return setStatus( SAT );
            }

            numeric * a;
            LAVar* y       = NULL;
            LAVar* y_found = NULL;

            // Model doesn't feet the lower bound
            if( x->M() < x->L() )
            {
                // look for nonbasic terms to fix the unbounding
                LARow::iterator it = x->polynomial.begin();
                for( ; it != x->polynomial.end(); x->polynomial.getNext( it ) )
                {
                    y = columns[it->key];
                    if( x == y )
                    {
                        continue;
                    }
                    //              cout << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                    assert( y->isNonbasic() );
                    a = it->coef;
                    const bool& a_is_pos = (*a) > 0;
                    if( (a_is_pos && y->M() < y->U()) || (!a_is_pos && y->M() > y->L()) )
                    {
                        if( bland_rule )
                        {
                            y_found = y;
                            break;    // stop on the very first that feats
                        }
                        else
                        {
                            if( y_found == NULL )
                            {
                                y_found = y;
                            }
                            else if( y_found->binded_rows.size() > y->binded_rows.size() )
                            {
                                y_found = y;
                            }
                        }
                    }
                }

                // if it was not found - UNSAT
                if( y_found == NULL )
                {
                    //              cout << "NO ways to SAT" << endl;
                    getConflictingBounds( x, mExplanation );
                    //TODO: Keep the track of updated models and restore only them
                    for( unsigned i = 0; i < columns.size(); ++i )
                    {
                        if( !columns[i]->skip )
                        {
                            columns[i]->restoreModel();
                        }
                    }
                    print( cout );
                    cout << endl << __LINE__ << "UNSAT" << endl;
                    return setStatus( UNSAT );
                }
                // if it was found - pivot old Basic x with non-basic y and do the model updates
                else
                {
                    pivotAndUpdate( x, y_found, x->L() );
                }
            }
            else if( x->M() > x->U() )
            {
                // look for nonbasic terms to fix the unbounding
                LARow::iterator it = x->polynomial.begin();
                for( ; it != x->polynomial.end(); x->polynomial.getNext( it ) )
                {
                    y = columns[it->key];
                    if( x == y )
                    {
                        continue;
                    }
                    //              cout << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

                    assert( y->isNonbasic() );
                    a = it->coef;
                    const bool& a_is_pos = (*a) > 0;
                    if( (!a_is_pos && y->M() < y->U()) || (a_is_pos && y->M() > y->L()) )
                    {
                        if( bland_rule )
                        {
                            y_found = y;
                            break;    // stop on the very first that feats
                        }
                        else
                        {
                            if( y_found == NULL )
                            {
                                y_found = y;
                            }
                            else if( y_found->binded_rows.size() > y->binded_rows.size() )
                            {
                                y_found = y;
                            }
                        }
                    }
                }

                // if it was not found - UNSAT
                if( y_found == NULL )
                {
                    //              cout << "NO ways to SAT 2" << endl;
                    // add the x to explanations
                    getConflictingBounds( x, mExplanation );
                    for( unsigned i = 0; i < columns.size(); ++i )
                        if( !columns[i]->skip )
                        {
                            columns[i]->restoreModel();
                        }
                    print( cout );
                    cout << endl << __LINE__ << "UNSAT" << endl;
                    return setStatus( UNSAT );
                }
                // if it was found - pivot old Basic x with non-basic y and do the model updates
                else
                {
                    pivotAndUpdate( x, y_found, x->U() );
                }
            }
            else
            {
                opensmt_error( "Error in bounds comparison" );
            }
        }
    }

    //
    // Push the constraint into the solver and increase the level
    //
    bool LRASolverA::assertLitA( const Constraint* const _constraint, bool _polarity )
    {
        cout << "assertLit " << _constraint->toString() << endl;
        // check if we stop reading constraints
        if( status == INIT )
        {
            initSolver();
        }

        LAVar* it = expressionLAVarMap[_constraint->lhs()];

        // Constraint to push was not find in local storage. Most likely it was not read properly before
        if( it == NULL )
        {
            opensmt_error( "Unexpected push !" );
        }

        assert( !it->isUnbounded() );
        unsigned index = it->getIteratorByExpression( _constraint->lhs(), !_polarity );

        if( assertBoundOnColumn( it, index ) )
        {
            //      if( lra_check_on_assert != 0 && rand() % 100 < lra_check_on_assert )
            //      {
            //          // force solver to do check on assert with some probability
            //          return checkA();
            //      }
        }
        return getStatus();
    }

    bool LRASolverA::assertBoundOnColumn( LAVar* _var, unsigned _index )
    {
        assert( status == SAT );
        assert( _var != NULL );
        assert( !_var->isUnbounded() );
        LAVar::LAVarBound& itBound = _var->all_bounds[_index];

        //  cout << "ASSERTING bound on " << *_var << endl;

        // Check is simple SAT can be given
        if( (itBound.mpBound_type && _index >= _var->u_bound) || (!itBound.mpBound_type && _index <= _var->l_bound) )
        {
            cout << __func__ << ":" << __LINE__ << endl;
            if( checks_history.back() < pushed_constraints.size() )
            {
                //          cout << "PUSH CHECK " << checks_history.back() << " " << pushed_constraints.size() << endl;
                checks_history.push_back( pushed_constraints.size() );
            }
            //      cout << "SIMPLE SAT" << endl;
            return getStatus();
        }
        // Check if simple UNSAT can be given
        if( (!itBound.mpBound_type && (_index > _var->u_bound)) || (itBound.mpBound_type && (_index < _var->l_bound)) )
        {
            cout << __func__ << ":" << __LINE__ << endl;
            mExplanation.clear();
            explanationCoefficients.clear();

            if( itBound.mpBound_type && _var->all_bounds[_var->l_bound].mVar != ex( 0 ) )
            {
                mExplanation.push_back( expressionOriginMap[_var->all_bounds[_var->l_bound].mVar] );
                explanationCoefficients.push_back( numeric( 1 ) );
            }
            else if( !itBound.mpBound_type && _var->all_bounds[_var->u_bound].mVar != ex( 0 ) )
            {
                mExplanation.push_back( expressionOriginMap[_var->all_bounds[_var->u_bound].mVar] );
                explanationCoefficients.push_back( numeric( 1 ) );
            }

            if( itBound.mVar != ex( 0 ) )
            {
                mExplanation.push_back( expressionOriginMap[itBound.mVar] );
                explanationCoefficients.push_back( numeric( -1 ) );
            }
            //      cout << "SIMPLE UNSAT" << endl;
            return setStatus( UNSAT );
        }

        //  cout << "write history" << endl;
        // Prepare the history entry
        LAVarHistory& hist = pushed_constraints.back();
        hist.mOrig      = itBound.mVar;
        hist.mpVariable = _var;
        hist.bound_type = itBound.mpBound_type;
        if( itBound.mpBound_type )
        {
            hist.bound    = _var->u_bound;
            _var->u_bound = _index;
        }
        else
        {
            hist.bound    = _var->l_bound;
            _var->l_bound = _index;
        }
        // Update the Tableau data if needed
        if( _var->isNonbasic() )    // && *( itBound.delta ) < _var->M() ) // && *( itBound.delta ) > _var->M() )
        {
            update( _var, *(itBound.mpDelta) );
        }

        //  LAVar *x = _var;
        //  cout << "ASSERTED bound on " << *x << ": " << x->L() << " <= " << x->M() << " <= " << x->U() << endl;

        //  cout << "NORMAL " << status <<endl;
        return getStatus();
    }

    //
    // Push the solver one level down
    //
    void LRASolverA::pushBacktrackPointA()
    {
        //  cout << "push " << pushed_constraints.size() << endl;
        // Check if any updates need to be repeated after backtrack
        if( first_update_after_backtrack )
        {
            //      cout << "re-apply " << pushed_constraints.size() << " - " << checks_history.back() << endl;
            for( unsigned i = checks_history.back(); i < pushed_constraints.size(); i++ )
            {
                LAVar* v = pushed_constraints[i].mpVariable;
                if( v != NULL && v->isNonbasic() && v->isModelOutOfBounds() )
                {
                    if( v->isModelOutOfUpperBound() )
                    {
                        update( v, v->U() );
                    }
                    else
                    {
                        update( v, v->L() );
                    }
                }
            }
            //      assertBoundOnColumn(pushed_constraints[i].mpVariable, pushed_constraints[i].bound, true);
            //      assertLitA( pushed_constraints[i].mpConstraint, false );

            //      for( unsigned i = 0; i < checks_history.size(); i++ )
            //      cout << checks_history[i] << " ";
            //      cout << endl;
            //      assert(checks_history.back() == pushed_constraints.size());
            first_update_after_backtrack = false;
        }

        // Create and push new history step
        LAVarHistory hist;
        hist.mOrig      = ex( 0 );
        hist.mpVariable = NULL;
        pushed_constraints.push_back( hist );
    }

    //
    // Pop the solver one level up
    //
    void LRASolverA::popBacktrackPointA()
    {
        //  cout << "pop " << pushed_constraints.size() << endl;

        // Undo with history
        LAVarHistory& hist = pushed_constraints.back();

        if( hist.mpVariable != NULL )
        {
            if( hist.bound_type )
            {
                hist.mpVariable->u_bound = hist.bound;
            }
            else
            {
                hist.mpVariable->l_bound = hist.bound;
            }
        }

        //TODO: Keep an eye on SAT model crossing the bounds of backtracking
        //  if( status == UNSAT && checks_history.back() == pushed_constraints.size() )
        if( checks_history.back() == pushed_constraints.size() )
        {
            //      cout << "POP CHECKS " << checks_history.back() << endl;
            checks_history.pop_back();
        }
        first_update_after_backtrack = true;

        pushed_constraints.pop_back();

        setStatus( SAT );
    }

    //
    // updates the model values according to asserted bound
    //
    void LRASolverA::update( LAVar* _var, const Delta& _delta )
    {
        // update model value for all basic terms
        const Delta& v_minusM = _delta - _var->M();
        for( LAColumn::iterator it = _var->binded_rows.begin(); it != _var->binded_rows.end(); _var->binded_rows.getNext( it ) )
        {
            LAVar& row = *(rows[it->key]);
            row.incM( *(row.polynomial[it->pos_in_row].coef) * v_minusM );

            if( static_cast<int>(row.polynomial.size()) <= lra_poly_deduct_size )
            {
                touched_rows.insert( rows[it->key] );
            }
        }
        _var->setM( _delta );
        //  cout << "UPDATED nonbasic " << *_var << ": " << _var->L() << " <= " << _var->M() << " <= " << _var->U() << endl;
    }

    //
    // pivots _varA and _varB in solver and does all updates
    //
    void LRASolverA::pivotAndUpdate( LAVar* _varA, LAVar* _varB, const Delta& _delta )
    {
        //  std::cout << "PIVOT AND UPDATE" << *_varA << " - " << *_varB << " - " << _delta << endl;
        assert( _varA != _varB );
        assert( _varA->isBasic() );
        assert( _varB->isNonbasic() );

        assert( _varB->polynomial.empty() );
        assert( _varA->binded_rows.empty() );
        assert( _varA->polynomial.exists( _varB->ID() ) );

        // get Tetta (zero if Aij is zero)
        const numeric& a = *(_varA->polynomial.find( _varB->ID() )->coef);
        assert( a != 0 );
        Delta tetha = (_delta - _varA->M()) / a;

        // update models of _varA and _varB
        _varA->setM( _delta );
        _varB->incM( tetha );

        // update model of Basic variables
        for( LAColumn::iterator it = _varB->binded_rows.begin(); it != _varB->binded_rows.end(); _varB->binded_rows.getNext( it ) )
        {
            if( rows[it->key] != _varA )
            {
                LAVar& row = *(rows[it->key]);
                row.incM( *(row.polynomial[it->pos_in_row].coef) * tetha );
                if( static_cast<int>(row.polynomial.size()) <= lra_poly_deduct_size )
                {
                    touched_rows.insert( rows[it->key] );
                }
            }
        }
        // pivoting _varA and _varB

        const numeric inverse = numeric( -1 ) / a;

        // OLD PIVOTING
        // first change the attribute values for _varA  polynomial
        for( LARow::iterator it = _varA->polynomial.begin(); it != _varA->polynomial.end(); _varA->polynomial.getNext( it ) )
        {
            *(it->coef) *= inverse;
        }

        // value of a_{_varB} should become -1
        assert( !(*(_varA->polynomial.find( _varB->ID() )->coef) != -1) );

        // now change the attribute values for all rows where _varB was presented
        for( LAColumn::iterator it = _varB->binded_rows.begin(); it != _varB->binded_rows.end(); _varB->binded_rows.getNext( it ) )
        {
            // check that the modified row is not _varA (it was changed already)
            if( rows[it->key] != _varA )
            {
                LAVar& row = *(rows[it->key]);

                assert( *(row.polynomial[it->pos_in_row].coef) != 0 );

                // copy a to the new numeric variable (use memory pool)
                //TODO: make a function for the code below
                numeric* p_a = NULL;
                if( !numbers_pool.empty() )
                {
                    p_a = numbers_pool.back();
                    numbers_pool.pop_back();
                    *p_a = *(row.polynomial[it->pos_in_row].coef);
                }
                else
                {
                    p_a = new numeric( *(row.polynomial[it->pos_in_row].coef) );
                }

                const numeric& a = *(p_a);

                // P_i = P_i + a_{_varB} * P_(_varA) (iterate over all elements of P(_varA))
                for( LARow::iterator it2 = _varA->polynomial.begin(); it2 != _varA->polynomial.end(); _varA->polynomial.getNext( it2 ) )
                {
                    LAVar&         col = *(columns[it2->key]);

                    const numeric& b   = *(it2->coef);
                    assert( b != 0 );
                    // insert new element to P_i
                    if( !row.polynomial.exists( it2->key ) )
                    {
                        // handle numerics via memory pool
                        numeric* p_c = NULL;
                        if( !numbers_pool.empty() )
                        {
                            p_c = numbers_pool.back();
                            numbers_pool.pop_back();
                            *p_c = a * b;
                        }
                        else
                        {
                            p_c = new numeric( a * b );
                        }
                        col.binded_rows.add( it->key, row.polynomial.add( it2->key, col.binded_rows.free_pos(), p_c ) );
                    }
                    // or add to existing
                    else
                    {
                        LARow::iterator a_it = row.polynomial.find( it2->key );
                        assert( a_it != row.polynomial.end() );
                        *(a_it->coef) += b * a;
                        if( *(a_it->coef) == 0 )
                        {
                            // delete element from P_i if it become 0
                            assert( a_it->coef );

                            // Save numeric in pool
                            numbers_pool.push_back( a_it->coef );

                            // Mark out the value from column and row
                            if( it2->key != _varB->ID() )
                            {
                                col.binded_rows.remove( a_it->pos );
                            }
                            row.polynomial.remove( a_it );
                        }
                    }
                }
                numbers_pool.push_back( p_a );

                assert( (row.polynomial.find( _varB->ID() ) == row.polynomial.end()) );

                // mark the affected row (for deductions)
                if( static_cast<int>(row.polynomial.size()) <= lra_poly_deduct_size )
                {
                    touched_rows.insert( rows[it->key] );
                }
            }
        }

        // swap _varA and _varB (basicID, polynomial, bindings)
        swap( _varA->polynomial, _varB->polynomial );
        assert( _varA->polynomial.empty() );
        assert( !_varB->polynomial.empty() );
        _varB->setBasic( _varA->basicID() );
        _varA->setNonbasic();
        rows[_varB->basicID()] = _varB;

        assert( _varB->polynomial.find( _varA->ID() ) != _varB->polynomial.end() );
        assert( _varB->polynomial.find( _varA->ID() )->pos >= 0 );
        assert( _varB->polynomial.find( _varA->ID() ) != _varB->polynomial.end() );
        const LARow::iterator tmp_it = _varB->polynomial.find( _varA->ID() );
        tmp_it->pos = _varA->binded_rows.free_pos();
        _varA->binded_rows.add( _varB->basicID(), _varB->polynomial.getPos( tmp_it ) );
        _varB->binded_rows.clear();

        if( static_cast<int>(_varB->polynomial.size()) <= lra_poly_deduct_size )
        {
            touched_rows.insert( _varB );
        }
        touched_rows.erase( _varA );

        assert( _varA->polynomial.size() == 0 );
        assert( _varB->polynomial.size() > 0 );
        assert( _varA->binded_rows.size() > 0 );
    }

    //
    // Perform all the required initialization after inform is complete
    //
    void LRASolverA::initSolver()
    {
        if( status == INIT )
        {
            status = SAT;
        }
        else
        {
            opensmt_error( "Solver can not be initialized in the state different from INIT" );
        }
    }

    ////
    // Returns boolean value correspondent to the current solver status
    //
    inline bool LRASolverA::getStatus()
    {
        switch( status )
        {
            case SAT:
            {
                return true;
            }
            case UNSAT:
            {
                return false;
            }
            case INIT:
            case ERROR:
            default:
            {
                opensmt_error( "Status is undef!" );
                return false;
            }
        }
    }

    //
    // Sets the new solver status and returns the correspondent Answer value
    //
    inline bool LRASolverA::setStatus( LRASolverStatus _status )
    {
        status = _status;
        return getStatus();
    }

    ////
    // Returns the bounds conflicting with the actual model.
    //
    void LRASolverA::getConflictingBounds( LAVar* _var, vector<const Constraint*>& _dst )
    {
        numeric * a;
        LAVar * y;
        if( _var->M() < _var->L() )
        {
            // add all bounds for polynomial elements, which limit lower bound
            LARow::iterator it = _var->polynomial.begin();
            for( ; it != _var->polynomial.end(); _var->polynomial.getNext( it ) )
            {
                a = it->coef;
                y = columns[it->key];
                assert( a );
                assert( (*a) != 0 );
                if( _var == y )
                {
                    if( y->all_bounds[y->l_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->l_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 1" <<endl;
                    }
                }
                else if( (*a) < 0 )
                {
                    assert( !y->L().isInf() );
                    if( y->all_bounds[y->l_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->l_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 2" <<endl;
                    }
                }
                else
                {
                    assert( !y->U().isInf() );
                    if( y->all_bounds[y->u_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->u_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 3" <<endl;
                    }
                }
            }
        }
        if( _var->M() > _var->U() )
        {
            // add all bounds for polynomial elements, which limit upper bound
            LARow::iterator it = _var->polynomial.begin();
            for( ; it != _var->polynomial.end(); _var->polynomial.getNext( it ) )
            {
                a = it->coef;
                y = columns[it->key];
                assert( a );
                assert( (*a) != 0 );
                if( _var == y )
                {
                    if( y->all_bounds[y->u_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->u_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 4" <<endl;
                    }

                }
                else if( (*a) > 0 )
                {
                    assert( !y->L().isInf() );
                    if( y->all_bounds[y->l_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->l_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 5" <<endl;
                    }
                }
                else
                {
                    assert( !y->U().isInf() );
                    if( y->all_bounds[y->u_bound].mVar != ex( 0 ) )
                    {
                        _dst.push_back( expressionOriginMap[y->all_bounds[y->u_bound].mVar] );
                        explanationCoefficients.push_back( *a );
                    }
                    else
                    {
                        //                  std::cout<< "WTF 6" <<endl;
                    }
                }
            }
        }

        //  cout << "CONFLICTING BOUNDS BEGIN" << endl;
        //  for( unsigned i = 0; i < _dst.size(); i++ )
        //  {
        //  cout << explanationCoefficients[i] << " * " << _dst[i] << endl;
        //  }
        //  cout << "CONFLICTING BOUNDS END" << endl;
        assert( _dst.size() == _var->polynomial.size() );
    }

    void LRASolverA::printExpressionLAVarMap( ostream& _out ) const
    {
        _out << "Expression LAVar map:" << endl;
        for( ExpressionLAVarMap::const_iterator iter = expressionLAVarMap.begin(); iter != expressionLAVarMap.end(); ++iter )
        {
            _out << "   " << iter->first << "  ->  " << iter->second << endl;
        }
    }

    void LRASolverA::printExpressionOriginMap( ostream& _out ) const
    {
        _out << "Expression origin map:" << endl;
        for( ExpressionConstraintMap::const_iterator iter = expressionOriginMap.begin(); iter != expressionOriginMap.end(); ++iter )
        {
            _out << "   " << iter->first << "  ->  " << iter->second->toString() << endl;
        }
    }

    void LRASolverA::printBacktrackPoints( ostream& _out ) const
    {
        _out << "Backtrack points:  ";
        for( vector<size_t>::const_iterator iter = backtrack_points.begin(); iter != backtrack_points.end(); ++iter )
        {
            _out << "                  " << *iter << endl;
        }
    }

    void LRASolverA::printPushedConstraints( ostream& _out ) const
    {
        _out << "Pushed constraints:" << endl;
        unsigned historyEntryNumber = 0;
        for( vector<LAVarHistory>::const_iterator iter = pushed_constraints.begin(); iter != pushed_constraints.end(); ++iter )
        {
            _out << "   " << "history entry #" << historyEntryNumber << endl;
            _out << "         mOrig      = " << iter->mOrig << endl;
            _out << "         mpVariable = " << *iter->mpVariable << endl;
            _out << "         bound      = " << iter->bound << endl;
            _out << "         bound_type = " << iter->bound_type << endl;
            ++historyEntryNumber;
        }
    }

    //
    // Prints the current state of the solver (terms, bounds, tableau)
    //
    void LRASolverA::print( ostream& _out )
    {
        //  printPushedConstraints();
        _out << endl << "Bounds:" << endl;

        // print bounds array size
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (*it)->all_bounds.size() << "\t";
        }
        _out << endl;

        // print the upper bounds
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (*it)->U() << "\t";
        }
        _out << endl;

        // print the lower bounds
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (*it)->L() << "\t";
        }
        _out << endl;

        // print current model values
        _out << "Var:" << endl;
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (**it).mVar << "\t";
        }
        _out << endl;

        // print current model values
        _out << "Model:" << endl;
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (*it)->M() << "\t";
        }
        _out << endl;

        // print the terms IDs
        _out << "Tableau:" << endl;
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << (*it)->ID() << "\t";
        }
        _out << endl;

        // print the Basic/Nonbasic status of terms
        for( VectorLAVar::iterator it = columns.begin(); it != columns.end(); ++it )
        {
            _out << ((*it)->isBasic() ? "B" : "N") << "\t";
        }
        _out << endl;

        // print the tableau cells (zeros are skipped)
        // iterate over Tableau rows
        for( unsigned i = 0; i < rows.size(); ++i )
        {
            for( VectorLAVar::iterator it2 = columns.begin(); it2 != columns.end(); ++it2 )
            {
                if( rows[i]->polynomial.find( (*it2)->ID() ) != rows[i]->polynomial.end() )
                {
                    _out << *(rows[i]->polynomial.find( (*it2)->ID() )->coef);
                }
                _out << "\t";
            }
            _out << endl;
        }
    }

    //
    // Detect the appropriate value for symbolic delta and dumps the model into Egraph
    //
    void LRASolverA::computeModel()
    {
        assert( status == SAT );

        numeric minDelta( 0 );
        numeric maxDelta( 0 );
        numeric curDelta( 0 );
        Delta curBound( Delta::ZERO );
        LAVar * col;

        //
        // For all columns check the min/max value for delta
        // Note, it should be always that min > 0 and max < 0
        //
        for( unsigned i = 0; i < columns.size(); ++i )
        {
            if( columns[i]->skip )
            {
                continue;
            }

            col = columns[i];
            assert( !col->isModelOutOfBounds() );

            curDelta = 0;
            curBound = Delta( Delta::ZERO );

            // Check if the lower bound can be used and at least one of delta and real parts are not 0
            if( !col->L().isInf() && (col->L().D() != 0 || col->M().D() != 0) && (col->L().R() != 0 || col->M().R() != 0) )
            {
                curBound = col->L() - col->M();

                // if denominator is >0 than use delta for min
                if( curBound.D() > 0 )
                {
                    curDelta = -(curBound.R() / curBound.D());
                    if( curDelta != 0 && (minDelta == 0 || minDelta > curDelta) )
                    {
                        minDelta = curDelta;
                    }
                }
                // if denominator is <0 than use delta for max
                else if( curBound.D() < 0 )
                {
                    curDelta = -(curBound.R() / curBound.D());
                    if( curDelta != 0 && (maxDelta == 0 || maxDelta < curDelta) )
                    {
                        maxDelta = curDelta;
                    }
                }
            }
            // Check if the upper bound can be used and at least one of delta and real parts are not 0
            if( !col->U().isInf() && (col->U().D() != 0 || col->M().D() != 0) && (col->U().R() != 0 || col->M().R() != 0) )
            {
                curBound = col->M() - col->U();

                // if denominator is >0 than use delta for min
                if( curBound.D() > 0 )
                {
                    curDelta = -(curBound.R() / curBound.D());
                    if( curDelta != 0 && (minDelta == 0 || minDelta > curDelta) )
                    {
                        minDelta = curDelta;
                    }
                }
                // if denominator is <0 than use delta for max
                else if( curBound.D() < 0 )
                {
                    curDelta = -(curBound.R() / curBound.D());
                    if( curDelta != 0 && (maxDelta == 0 || maxDelta < curDelta) )
                    {
                        maxDelta = curDelta;
                    }
                }
            }
        }

        // TODO: check if it is it really true :)
        assert( minDelta >= 0 );
        assert( maxDelta <= 0 );
        curDelta = (minDelta) / 2;
        //  cout << "Delta: " << max << " < " << cur << " < " << min <<endl;

        // Compute the value for each variable. Delta is taken into account
        for( unsigned i = 0; i < columns.size(); ++i )
        {
            if( !(columns[i]->skip) )
            {
                columns[i]->computeModel( curDelta );
            }
        }
    }

    //
    //
    //
    void LRASolverA::addVarToRow( LAVar* _slackVar, LAVar* _var, numeric* _pivotValue )
    {
        if( _var->isNonbasic() )
        {
            LARow::iterator p_it = _slackVar->polynomial.find( _var->ID() );
            if( p_it != _slackVar->polynomial.end() )
            {
                *(p_it->coef) += *_pivotValue;
                if( *(p_it->coef) == 0 )
                {
                    numbers_pool.push_back( p_it->coef );
                    _var->binded_rows.remove( p_it->pos );
                    _slackVar->polynomial.remove( p_it );
                    //              _var->unbindRow( _slackVar->basicID() );
                }
            }
            else
            {
                _var->binded_rows.add( _slackVar->basicID(), _slackVar->polynomial.add( _var->ID(), _var->binded_rows.free_pos(), _pivotValue ) );
                //          _slackVar->polynomial.add( _var->ID(), _pivotValue );
                //          _var->bindRow( _slackVar->basicID(), _pivotValue );
            }
        }
        else
        {
            LARow::iterator it = _var->polynomial.begin();
            for( ; it != _var->polynomial.end(); _var->polynomial.getNext( it ) )
            {
                if( _var->ID() == it->key )
                    continue;

                assert( columns[it->key]->isNonbasic() );

                numeric * tmp_r;

                if( !numbers_pool.empty() )
                {
                    tmp_r = numbers_pool.back();
                    numbers_pool.pop_back();
                    *tmp_r = numeric( *(it->coef) * (*_pivotValue) );
                }
                else
                {
                    tmp_r = new numeric( *(it->coef) * (*_pivotValue) );
                }
                LARow::iterator p_it = _slackVar->polynomial.find( it->key );
                if( p_it != _slackVar->polynomial.end() )
                {
                    *(p_it->coef) += *tmp_r;
                    numbers_pool.push_back( tmp_r );
                    if( *(p_it->coef) == 0 )
                    {
                        numbers_pool.push_back( p_it->coef );
                        columns[it->key]->binded_rows.remove( p_it->pos );
                        _slackVar->polynomial.remove( p_it );
                    }
                }
                else
                {
                    columns[it->key]->binded_rows.add( _slackVar->basicID(),
                                                       _slackVar->polynomial.add( it->key, columns[it->key]->binded_rows.free_pos(), tmp_r ) );
                    //              _slackVar->polynomial.add( it->key, tmp_r );
                    //              columns[it->key]->bindRow( _slackVar->basicID(), tmp_r );
                }
            }
            numbers_pool.push_back( _pivotValue );
        }
    }

}    // end namspace vs

