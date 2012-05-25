/*********************************************************************
Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
      , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef LAVAR_H
#define LAVAR_H

#include "Delta.h"
#include "LARow.h"
#include "LAColumn.h"
#include "../../Constraint.h"

namespace lra
{

//
// Class to store the term of constraints as a column of Simplex method tableau
//
class LAVar
{
public:
  // structure to store bound information
  struct LAVarBound
  {
    GiNaC::ex 	mVar;
    Delta* 		mpDelta;
    bool 		mpBound_type;
    bool 		mpReverse;
    bool 		mpActive;
    
    LAVarBound( Delta* _delta, const GiNaC::ex _var, bool _boundType, bool _reverse );
    bool operator==( const LAVarBound& _bound );
  };

private:
  typedef std::vector<LAVarBound> VectorBounds; 	// type for bounds storage


  /*
   * Members
   */
  static Delta 		plus_inf_bound;         // used for a default +inf value, which is shared by every LAVar
  static Delta 		minus_inf_bound;        // used for a default -inf value, which is shared by every LAVar

  static int 		column_count;           // Static counter to create ID for LAVar
  static int 		row_count;              // Static counter for rows keep track of basic variables

  static unsigned 	model_global_counter;   // global counter used to inform all the LAVar if they are different from the last saved point
  unsigned 			model_local_counter;    // local counter used to decide when the model should be switched

  int 				column_id;              // ID (column number) for LAVar
  int 				row_id;                 // row_id (row number) for LAVar. For public known as basicID :)

  Delta* 			m1;                     // one of two storages used by model switching
  Delta* 			m2;                     // one of two storages used by model switching

public:
  GiNaC::ex			mVar;         			// pointer to original Enode. In case of slack variable points to polynomial
  GiNaC::numeric	mValue;					// current assignment of the variable
  LARow 			polynomial;      		// elements of the variable polynomial (if variable is basic), list of <id, GiNaC::numeric*>
  LAColumn 			binded_rows;     		// rows a variable is binded to (if it is nonbasic) ,list of <id, GiNaC::numeric*>
  bool 				skip;             		// used to skip columns deleted during Gaussian
  VectorBounds 		all_bounds;				// array storage for all bounds of the variable
  unsigned 			u_bound;      			// integer pointer to the current upper bound
  unsigned 			l_bound;      			// integer pointer to the current lower bound

  /*
   * Constructors
   */
  LAVar( const GiNaC::ex _orig);                                              					// Default constructor
  LAVar( const GiNaC::ex _orig, GiNaC::numeric& _bound, const GiNaC::ex _var, bool _basic );  		// Constructor with bounds
  LAVar( const GiNaC::ex _orig, const GiNaC::ex _var, const GiNaC::numeric& _value, bool _revert );   // Constructor with bounds from real
  
  /*
   * Destructor
   */
  virtual ~LAVar( );
  
  /*
   * Methods
   */
  void setBounds( const GiNaC::ex _var, const GiNaC::numeric& _value );   // Set the bounds according to enode type and a given value (used on reading/construction stage)

  unsigned setUpperBound( const GiNaC::numeric& _value );
  unsigned setLowerBound( const GiNaC::numeric& _value );

  unsigned setBound( const GiNaC::numeric& _value, bool _upper);
  void addBoundsAndUpdateSorting(const LAVarBound& _boundA, const LAVarBound& _boundB );
  void addBoundAndUpdateSorting(const LAVarBound& _bound );
  void updateSorting();

  unsigned getBoundByValue( const GiNaC::numeric& _value, bool _upper);

  void sortBounds( );   // sort bounds' list
  void printBounds( );  // print out bounds' list

  unsigned getIteratorByExpression( const GiNaC::ex, bool );        // find bound iterator by the correspondent Enode ID

  inline bool isBasic( );               // Checks if current LAVar is Basic in current solver state
  inline bool isNonbasic( );            // Checks if current LAVar is NonBasic in current solver state
  inline bool isModelOutOfBounds( );    // Check if current Model for LAVar does not feat into the bounds.
  inline bool isModelOutOfLowerBound( );// Check if current Model for LAVar does not feat into the lower bound.
  inline bool isModelOutOfUpperBound( );// Check if current Model for LAVar does not feat into the upper bound.
  inline bool isUnbounded( );           // Check if LAVar has no bounds at all (it can be eliminated if possible).
  inline bool isModelInteger( );        // Check if LAVar has an integer model.
  inline bool isEquality();
  inline const Delta overBound();

  inline int ID( );                             // Return the ID of the LAVar
  inline int basicID( );                        // Return the basicID (row id) of the basic LAVar (-1 if it is Nonbasic)
  inline void setNonbasic( );                   // Make LAVar Nonbasic
  inline void setBasic( int _row );              // Make LAVar Basic and set the row number it corresponds
  inline void unbindRow( int _row );             // remove row from the binding list
  inline void saveModel( );                     // save model locally
  inline void restoreModel( );                  // restore to last globally saved model
  static inline void saveModelGlobal( );        // save model globally
  void computeModel( const GiNaC::numeric& b = 0 );       // save the actual model to Egraph

  inline const Delta& U( ); // The latest upper bound of LAVar (+inf by default)
  inline const Delta& L( ); // The latest lower bound of LAVar (-inf by default)
  inline const Delta& M( ); // The latest model of LAVar (0 by default)

  inline void incM( const Delta& _bound ); // increase actual model by _bound
  inline void setM( const Delta& _bound ); //set actual model to _bound
  
  inline GiNaC::numeric getValue(); //
  inline void setValue( const GiNaC::numeric& );

  inline friend std::ostream & operator <<( std::ostream& _out, LAVar& _lavar )
  {
    _out << &_lavar;
    return _out;
  }

  // structure to perform comparison of two LAVarBounds
  struct LAVarBounds_ptr_cmp
  {
    bool operator()( LAVarBound lhs, LAVarBound rhs );
  };
};

bool LAVar::isBasic( )
{
  return ( row_id != -1 );
}

bool LAVar::isModelOutOfBounds( )
{
  return ( M( ) > U( ) || M( ) < L( ) );
}

bool LAVar::isModelOutOfUpperBound( )
{
  return ( M( ) > U( ));
}

bool LAVar::isModelOutOfLowerBound( )
{
  return ( M( ) < L( ));
}


const Delta LAVar::overBound( )
{
  assert( isModelOutOfBounds( ) );
  if( M( ) > U( ) )
  {
    return ( Delta(M( ) - U( )));
  }
  else if ( M( ) < L( ))
  {
    return ( Delta(L( ) - M( )) );
  }
  assert (false);
}


bool LAVar::isModelInteger( )
{
  return !( M( ).hasDelta() || M().R().denom() != 1);
}

bool LAVar::isEquality( )
{
  if( l_bound + 1 == u_bound && !L( ).isInf( ) && !U( ).isInf( ) && all_bounds[l_bound].mpDelta == all_bounds[u_bound].mpDelta )
    return true;
  else
    return false;
}

bool LAVar::isUnbounded( )
{
  return all_bounds.size( ) < 3;
}

bool LAVar::isNonbasic( )
{
  return !isBasic( );
}

int LAVar::ID( )
{
  return column_id;
}

int LAVar::basicID( )
{
  return row_id;
}

void LAVar::setNonbasic( )
{
  row_id = -1;
}

void LAVar::setBasic( int _row )
{
  row_id = _row;
}

void LAVar::unbindRow( int _row )
{
  assert( this->binded_rows.find( _row ) != this->binded_rows.end( ) || this->isBasic( ) );
  this->binded_rows.remove( this->binded_rows.find( _row ) );
}

void LAVar::saveModel( )
{
  *m2 = *m1;
  model_local_counter = model_global_counter;
}

void LAVar::saveModelGlobal( )
{
  model_global_counter++;
}

void LAVar::restoreModel( )
{
  if( model_local_counter == model_global_counter )
  {
    *m1 = *m2;
    model_local_counter--;
  }
}

const Delta & LAVar::U( )
{
  assert( all_bounds[u_bound].mpDelta );
  return *( all_bounds[u_bound].mpDelta );
}

const Delta & LAVar::L( )
{
  assert( all_bounds[l_bound].mpDelta );
  return *( all_bounds[l_bound].mpDelta );
}

const Delta & LAVar::M( )
{
  return ( *m1 );
}

void LAVar::incM( const Delta& _bound )
{
  setM( M( ) + _bound );
}

void LAVar::setM( const Delta& _bound )
{
  if( model_local_counter != model_global_counter )
    saveModel( );
  ( *m1 ) = _bound;
}

GiNaC::numeric LAVar::getValue()
{
	return mValue;
}

void LAVar::setValue( const GiNaC::numeric& _value )
{
	mValue = _value;
}

}     // end namspace vs

#endif
