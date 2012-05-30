/*
 * Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 * Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 *
 * OpenSMT -- Copyright (C) 2007, Roberto Bruttomesso
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


#include "LAVar.h"

using namespace std;
using namespace GiNaC;

namespace lra
{
    int      LAVar::column_count         = 0;
    int      LAVar::row_count            = 0;

    Delta    LAVar::plus_inf_bound       = Delta( Delta::UPPER );
    Delta    LAVar::minus_inf_bound      = Delta( Delta::LOWER );

    unsigned LAVar::model_global_counter = 1;

    //
    // Default constructor
    //
    LAVar::LAVar( const ex _orig = ex( 0 ) )
    {
        column_id = column_count++;
        row_id    = -1;
        skip      = false;

        // zero as default model
        m1                  = new Delta( Delta::ZERO );
        m2                  = new Delta( Delta::ZERO );
        model_local_counter = 0;

        ex null             = ex( 0 );
        LAVarBound pb1( &minus_inf_bound, null, false, false );
        LAVarBound pb2( &plus_inf_bound, null, true, false );
        all_bounds.push_back( pb1 );
        all_bounds.push_back( pb2 );
        u_bound = 1;
        l_bound = 0;

        mVar    = _orig;
    }

    //
    // Constructor with bounds initialization
    //
    LAVar::LAVar( const ex _orig, numeric& _bound, const ex _var, bool _basic = false )
    {
        column_id = column_count++;

        if( _basic )
            row_id = row_count++;
        else
            row_id = -1;

        skip = false;

        // zero as default model
        m1                  = new Delta( Delta::ZERO );
        m2                  = new Delta( Delta::ZERO );
        model_local_counter = 0;

        ex null             = ex( 0 );
        LAVarBound pb1( &minus_inf_bound, null, false, false );
        LAVarBound pb2( &plus_inf_bound, null, true, false );
        all_bounds.push_back( pb1 );
        all_bounds.push_back( pb2 );
        u_bound = 1;
        l_bound = 0;

        mVar    = _var;
        // set original bounds from Enode
        setBounds( _orig, _bound );
    }

    LAVar::LAVar( const ex _orig, const ex _var, const numeric& _value, bool _revert )
    {
        column_id = column_count++;
        row_id    = -1;

        skip      = false;

        // zero as default model
        m1                  = new Delta( Delta::ZERO );
        m2                  = new Delta( Delta::ZERO );
        model_local_counter = 0;

        ex null             = ex( 0 );
        LAVarBound pb1( &minus_inf_bound, null, false, false );
        LAVarBound pb2( &plus_inf_bound, null, true, false );
        all_bounds.push_back( pb1 );
        all_bounds.push_back( pb2 );
        u_bound = 1;
        l_bound = 0;

        mVar    = _var;

        // set original bounds from Enode
        setBounds( _orig, _value );

    }

    LAVar::~LAVar()
    {
        // Remove bounds
        while( !all_bounds.empty() )
        {
            assert( all_bounds.back().mpDelta );
            if( all_bounds.back().mpDelta != &minus_inf_bound && all_bounds.back().mpDelta != &plus_inf_bound )
                delete all_bounds.back().mpDelta;
            all_bounds.pop_back();
        }
        // Remove polynomial coefficients
        for( LARow::iterator it = polynomial.begin(); it != polynomial.end(); polynomial.getNext( it ) )
        {
            assert( it->coef );
            if( it->key != -2 )
                delete it->coef;
            //    it->second = NULL;
        }

        delete (m2);
        delete (m1);
    }

    //
    // Reads the type of the bounds from enode type
    //
    void LAVar::setBounds( const ex _var, const numeric& _value )
    {
        //TODO: What is revert?
        bool             revert       = true;

        Delta*           bound        = NULL;
        Delta*           boundRev     = NULL;

        Delta::deltaType mpBound_type = Delta::UPPER;

        bound = new Delta( _value );

        if( revert )
        {
            boundRev = new Delta( _value, 1 );
        }
        else
        {
            boundRev     = new Delta( _value, -1 );
            mpBound_type = Delta::LOWER;
        }

        assert( bound );
        assert( boundRev );
        assert( bound != boundRev );

        LAVarBound pb1( bound, _var, (mpBound_type == Delta::UPPER), false );
        LAVarBound pb2( boundRev, _var, (mpBound_type != Delta::UPPER), true );

        addBoundsAndUpdateSorting( pb1, pb2 );
    }

    unsigned LAVar::setUpperBound( const numeric& _value )
    {
        return setBound( _value, true );
    }

    unsigned LAVar::setLowerBound( const numeric& _value )
    {
        return setBound( _value, false );
    }

    unsigned LAVar::setBound( const numeric& _value, bool _upper )
    {
        unsigned i = getBoundByValue( _value, _upper );
        if( i != 0 )
            return i;

        Delta*           bound        = NULL;

        Delta::deltaType mpBound_type = (_upper ? Delta::UPPER : Delta::LOWER);

        bound = new Delta( _value );

        assert( bound );

        LAVarBound pb( bound, ex( 0 ), (mpBound_type == Delta::UPPER), false );

        addBoundAndUpdateSorting( pb );
        return getBoundByValue( _value, _upper );
    }

    void LAVar::addBoundsAndUpdateSorting( const LAVarBound& _boundA, const LAVarBound& _boundB )
    {
        all_bounds.push_back( _boundA );
        all_bounds.push_back( _boundB );

        updateSorting();
    }

    void LAVar::addBoundAndUpdateSorting( const LAVarBound& _bound )
    {
        all_bounds.push_back( _bound );

        updateSorting();
    }

    void LAVar::updateSorting()
    {
        // save currently active bounds
        assert( all_bounds.size() > 1 && u_bound < all_bounds.size() && l_bound < all_bounds.size() );

        all_bounds[u_bound].mpActive = true;
        all_bounds[l_bound].mpActive = true;

        //TODO: Instead of sorting all bounds after insertion,
        //      I should check if it fits on left(right) of current pointers and sort only there
        sortBounds();
        //  printBounds();

        int i;
        // restore lower bound
        if( all_bounds[l_bound].mpActive )
        {
            all_bounds[l_bound].mpActive = false;
        }
        else
        {
            for( i = 0; i < static_cast<int>(all_bounds.size()); ++i )
            {
                if( !all_bounds[i].mpBound_type && all_bounds[i].mpActive )
                {
                    l_bound                = i;
                    all_bounds[i].mpActive = false;
                    break;
                }
            }
            assert( i != static_cast<int>(all_bounds.size()) );
        }

        // restore upper bound
        if( all_bounds[u_bound].mpActive )
        {
            all_bounds[u_bound].mpActive = false;
        }
        else
        {
            for( i = all_bounds.size() - 1; i >= 0; --i )
            {
                if( all_bounds[i].mpBound_type && all_bounds[i].mpActive )
                {
                    u_bound                      = i;
                    all_bounds[u_bound].mpActive = false;
                    break;
                }
            }
            assert( i != 0 );
        }

    }

    //
    // Finds the bound from the bound list that correspond to the given Enode and polarity
    //
    //TODO:: Can I do better here? Iterate from different sides? - YES
    unsigned LAVar::getIteratorByExpression( const ex _orig, bool _reverse )
    {
        unsigned it;
        it = all_bounds.size() - 2;
        assert( it != 0 );
        while( it > 0 &&!(all_bounds[it].mVar == _orig && all_bounds[it].mpReverse == _reverse) )
            --it;
        assert( it != 0 );    // we assume Enode is in!
        return it;
    }

    unsigned LAVar::getBoundByValue( const numeric& _value, bool _upper )
    {
        unsigned it = all_bounds.size() - 2;
        assert( it != 0 );
        while( it > 0 &&!(all_bounds[it].mpDelta->R() == _value && all_bounds[it].mpBound_type == _upper) )
            --it;
        return it;
    }

    //
    // Sorts the bounds on the list
    //
    void LAVar::sortBounds()
    {
        sort( all_bounds.begin(), all_bounds.end(), LAVarBounds_ptr_cmp() );

        u_bound = all_bounds.size() - 1;
        l_bound = 0;

    }

    //
    // Computes the model and pushes it to the correspondent Enode (delta is taken into account)
    //
    void LAVar::computeModel( const numeric& _value )
    {
        assert( !isModelOutOfBounds() );
        this->setValue( M().R() + _value * M().D() );
    }

    //
    // Prints the bounds of the LAVar
    //
    void LAVar::printBounds()
    {
        cerr << endl << this << " | ";
        for( unsigned i = 0; i < all_bounds.size(); i++ )
            cerr << *(all_bounds[i].mpDelta) << (all_bounds[i].mpBound_type ? "[U]" : "[L]") << (all_bounds[i].mpReverse ? "rev" : "") << " ";
    }

    bool LAVar::LAVarBounds_ptr_cmp::operator ()( LAVarBound _boundA, LAVarBound _boundB )
    {
        assert( _boundA.mpDelta );
        assert( _boundB.mpDelta );
        if( _boundA == _boundB )
            return true;
        else if( !_boundA.mpDelta->isInf() &&!_boundB.mpDelta->isInf() && _boundA.mpDelta->R() == _boundB.mpDelta->R() )
        {
            if( _boundA.mpBound_type == _boundB.mpBound_type )
            {
                // if this assertion fails then you have duplicates in the bounds list. Check the canonizer.
                //cout << _boundA.mpDelta->D() << " != " << _boundB.mpDelta->D() << " ? " << ((_boundA.mpDelta->D( ) != _boundB.mpDelta->D( )) ? "yes" : "no") << endl;
                cout << "assert( _boundA.mpDelta->D( ) != _boundB.mpDelta->D( ) );" << endl;
                //      assert( _boundA.mpDelta->D( ) != _boundB.mpDelta->D( ) );
                if( _boundA.mpBound_type )
                    return (_boundA.mpDelta->D() == 1 || _boundA.mpDelta->D() == -1);
                else
                    return (_boundA.mpDelta->D() == 0);
            }
            else if( _boundA.mpBound_type )
                return (_boundA.mpDelta->D() == 1 || _boundA.mpDelta->D() == -1 || _boundB.mpDelta->D() == 1);
            else
                return (_boundA.mpDelta->D() == 0 && _boundB.mpDelta->D() == 0);
        }
        else
            return *(_boundA.mpDelta) < *(_boundB.mpDelta);
    }

    LAVar::LAVarBound::LAVarBound( Delta* _delta, const ex _var, bool _boundType, bool _reverse )
    {
        mpDelta      = _delta;
        mVar         = _var;
        mpBound_type = _boundType;
        mpReverse    = _reverse;
        mpActive     = false;
    }

    bool LAVar::LAVarBound::operator ==( const LAVarBound& _bound )
    {
        if( (this->mVar == _bound.mVar) && (this->mpDelta == _bound.mpDelta) && (this->mpBound_type == _bound.mpBound_type)
                && (this->mpReverse == _bound.mpReverse) )
            return true;
        else
            return false;
    }

}    // end namspace vs

