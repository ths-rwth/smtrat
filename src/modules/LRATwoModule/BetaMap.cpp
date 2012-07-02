/*
 * BetaMap.cpp
 *
 *  Created on: May 4, 2012
 *      Author: Cullen
 */

#include "BetaMap.h"

using namespace std;
using namespace GiNaC;

namespace smtrat
{
    BetaMap::BetaMap():
        map()
    {}

    //    BetaMap::BetaMap(GiNaC::ex var, Real beta){
    //
    //    }

    BetaMap::~BetaMap(){}

    Real BetaMap::getBeta( const ex var ) const
    {
        map<const ex, Real>::const_iterator it;
        it = this->find( var );
        if( it != this->end() )
        {
            return it->second;
        }
        return Real( 0, false );
    }

    void BetaMap::setBeta( ex var, Real beta )
    {
        this->insert( pair<const ex, Real>( var, beta ) );
    }

    string BetaMap::toString()
    {
        string output = "BetaMap:\n";
        for( map<const ex, Real>::const_iterator betaVal = this->begin(); betaVal != this->end(); ++betaVal )
        {
            output += "The beta value of variable ";
            ostringstream stream;
            string        value;
            stream << (betaVal->first);
            Real beta = betaVal->second;
            value     = beta.toString();
            output    += stream.str();
            output    += " is ";
            output    += value;
            output    += "\n";
        }
        return output;
    }

    /**
         *  Update all beta values of all basic variables with nonzero coefficient in column nonbasic in the current Simplex Tableaux according to pivoting algorithm.
         *
                 * @param tab       The current Simplex Tableaux.
                 * @param basic         The basic variable for pivoting.
         * @param nonbasic  The corresponding nonbasic variable chosen for pivoting.
         * @param value     The value is the upper (resp. lower) bound the basic variable is set to by pivoting.
         *
         */
    //      void BetaMap::updateBeta( SimplexTableaux tab, ex basic, ex nonbasic, Real value ) {
    //
    //          bool nonbasicExisting = true;
    //          bool basicExisting = true;
    //          bool currBasicVarExisting=true;
    //          Real nonbasicBeta;
    //          Real basicBeta;
    //          Real currBasicBeta;
    //          Real updateVal;
    //          // do this with every map.at() call if you are not sure (100%) that the entry exists.
    //          // we have to test if the entry exists, if not there is an exception that is thrown!
    //          //get the basic variable's current beta value needed to compute updateVal (see below)
    //          try {
    //              basicBeta = this->at(basic);
    //          }
    //          catch ( ... ) {
    //          basicExisting = false;
    //      };
    //          try {
    //              nonbasicBeta=this->at(nonbasic);
    //          }
    //          catch ( ... ) {
    //              nonbasicExisting = false;
    //          };
    //          //getEntry returns bool stating whether coefficient exists in tableaux and the coefficient (Real) in case it exists
    //          pair<bool, numeric> entry = tab.getEntry(basic, nonbasic);
    //
    //
    //          //TODO: do we have to ask for basicExisting and nonbasicExisting here?! if one of them is false
    //          // then we should never get to this line (exception thrown)
    //          if (entry.first && basicExisting && nonbasicExisting) {
    //
    //
    //              numeric denominator = entry.second;
    //              //updateVal is the value with which each beta-value of every var has to be updated
    //              updateVal = (value - basicBeta) / denominator;
    //              //update variables used for pivoting
    //              //note that basic and nonbasic vars must exist since tab.getEntry(..) returned entry.first=true
    //              this->at(basic) = value;
    //              this->at(nonbasic) = this->at(nonbasic) + updateVal;
    //              //update all remaining basic variables
    //              map<ex, int, ex_is_less> basicVars = tab.getBasics();
    //              basicVars.erase(basic);
    //              for (map<ex, int>::iterator var = basicVars.begin(); var != basicVars.end(); ++var) {
    //                  try {
    //                  currBasicBeta=this->at(var->first);
    //              }
    //              catch ( exception &e ) {
    //                  currBasicVarExisting = false;
    //              };
    //
    //                  entry = tab.getEntry(var->first, nonbasic);
    //                  // TODO does != suffice to compare two ex instances??
    //                  if (entry.first){
    // //                   if(var->first != basic){
    //                          currBasicBeta = currBasicBeta + tab.getEntry(var->first, nonbasic).second * updateVal;
    //                          this->at(var->first)= currBasicBeta;
    ////                    }
    //                  } else {
    //                      string output;
    //                  ostringstream stream1;
    //                  ostringstream stream2;
    //                  stream1 << var->first;;
    //                  output += stream1.str();
    //                  output += ", ";
    //                  stream2 << nonbasic;
    //                  output += stream2.str();
    //                  cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //                  }
    //              }
    //          } else {
    ////             This part happens only if the entry wanted is zero!!!
    //              // TODO: the pair of vars chosen for pivoting or the nonbasic variable's coefficient
    //              // does not exist, react properly!
    //              // is this enough?
    //              string output;
    //              ostringstream stream1;
    //              ostringstream stream2;
    //              stream1 << basic;
    //              output += stream1.str();
    //              output += ", ";
    //              stream2 << nonbasic;
    //              output += stream2.str();
    //              cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //          }
    //
    //      }

    //      /**
    //           *  Update all beta values of all basic variables with nonzero coefficient in nonbasic column in the current Simplex Tableaux when a new upper or lower bound was asserted.
    //           *
    //           * @param tab               The current Simplex Tableaux.
    //       * @param nonbasic          The nonbasic variable for which an upper (resp. lower) bound was asserted.
    //       * @param upperCandidate    The upperCandidate is the asserted upper (resp. lower) bound of the nonbasic variable.
    //           *
    //           */
    //  void BetaMap::upateBeta2( SimplexTableaux tab, ex nonbasic, Real candidate){
    //      bool nonbasicExisting = true;
    //      bool currBasicVarExisting=true;
    //      Real nonbasicBeta;
    //      Real currBasicBeta;
    //      Real updateVal;
    //      try {
    //          nonbasicBeta=this->at(nonbasic);
    //      }
    //      catch ( exception &e ) {
    //          nonbasicExisting = false;
    //      };
    //      updateVal = candidate - nonbasicBeta;
    //      this->at(nonbasic) = candidate;
    //      map<ex, int, ex_is_less> basicVars = tab.getBasics();
    //      pair<bool, numeric> entry;
    //      for (map<ex, int>::iterator var = basicVars.begin(); var != basicVars.end(); ++var) {
    //          entry=tab.getEntry(var->first, nonbasic);
    //
    //          //TODO: do we have to ask for nonbasicExisting here?! if it was false
    //          // then we should never get to this line (exception thrown)
    //          if (entry.first && nonbasicExisting) {
    //              try {
    //                  currBasicBeta=this->at(var->first);
    //              }
    //              catch ( exception &e ) {
    //                  currBasicVarExisting = false;
    //              };
    //              currBasicBeta = currBasicBeta + tab.getEntry(var->first, nonbasic).second * updateVal;
    //              this->at(var->first) = currBasicBeta;
    //          } else {
    //              string output;
    //              ostringstream stream1;
    //              ostringstream stream2;
    //              stream1 << var->first;
    //              output += stream1.str();
    //              output += ", ";
    //              stream2 << nonbasic;
    //              output += stream2.str();
    //              cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //          }
    //
    //      }
    //
    //  }

    //<<<<<<< .mine
    //
    //          //TODO: do we have to ask for basicExisting and nonbasicExisting here?! if one of them is false
    //          // then we should never get to this line (exception thrown)
    //          if (entry.first && basicExisting && nonbasicExisting) {
    //
    //
    //              numeric denominator = entry.second;
    //              //updateVal is the value with which each beta-value of every var has to be updated
    //              updateVal = (value - basicBeta) / denominator;
    //              //update variables used for pivoting
    //              //note that basic and nonbasic vars must exist since tab.getEntry(..) returned entry.first=true
    //              this->at(basic) = value;
    //              this->at(nonbasic) = this->at(nonbasic) + updateVal;
    //              //update all remaining basic variables
    //              map<ex, int, ex_is_less> basicVars = tab.getBasics();
    //              basicVars.erase(basic);
    //              for (map<ex, int>::iterator var = basicVars.begin(); var != basicVars.end(); ++var) {
    //                  try {
    //                  currBasicBeta=this->at(var->first);
    //              }
    //              catch ( exception &e ) {
    //                  currBasicVarExisting = false;
    //              };
    //
    //                  entry = tab.getEntry(var->first, nonbasic);
    //                  // TODO does != suffice to compare two ex instances??
    //                  if (entry.first){
    // //                   if(var->first != basic){
    //                          currBasicBeta = currBasicBeta + tab.getEntry(var->first, nonbasic).second * updateVal;
    //                          this->at(var->first)= currBasicBeta;
    ////                    }
    //                  } else {
    //                      string output;
    //                  ostringstream stream1;
    //                  ostringstream stream2;
    //                  stream1 << var->first;;
    //                  output += stream1.str();
    //                  output += ", ";
    //                  stream2 << nonbasic;
    //                  output += stream2.str();
    //                  cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //                  }
    //              }
    //          } else {
    ////             This part happens only if the entry wanted is zero!!!
    //              // TODO: the pair of vars chosen for pivoting or the nonbasic variable's coefficient
    //              // does not exist, react properly!
    //              // is this enough?
    //              string output;
    //              ostringstream stream1;
    //              ostringstream stream2;
    //              stream1 << basic;
    //              output += stream1.str();
    //              output += ", ";
    //              stream2 << nonbasic;
    //              output += stream2.str();
    //              cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //          }
    //
    //      }
    //
    //      /**
    //           *  Update all beta values of all basic variables with nonzero coefficient in nonbasic column in the current Simplex Tableaux when a new upper or lower bound was asserted.
    //           *
    //                 * @param tab         The current Simplex Tableaux.
    //       * @param nonbasic      The nonbasic variable for which an upper (resp. lower) bound was asserted.
    //       * @param upperCandidate    The upperCandidate is the asserted upper (resp. lower) bound of the nonbasic variable.
    //           *
    //           */
    //  void BetaMap::upateBeta2( SimplexTableaux tab, ex nonbasic, Real candidate){
    //      bool nonbasicExisting = true;
    //      bool currBasicVarExisting=true;
    //      Real nonbasicBeta;
    //      Real currBasicBeta;
    //      Real updateVal;
    //      try {
    //          nonbasicBeta=this->at(nonbasic);
    //      }
    //      catch ( exception &e ) {
    //          nonbasicExisting = false;
    //      };
    //      updateVal = candidate - nonbasicBeta;
    //      this->at(nonbasic) = candidate;
    //      map<ex, int, ex_is_less> basicVars = tab.getBasics();
    //      pair<bool, numeric> entry;
    //      for (map<ex, int>::iterator var = basicVars.begin(); var != basicVars.end(); ++var) {
    //          entry=tab.getEntry(var->first, nonbasic);
    //
    //          //TODO: do we have to ask for nonbasicExisting here?! if it was false
    //          // then we should never get to this line (exception thrown)
    //          if (entry.first && nonbasicExisting) {
    //              try {
    //                  currBasicBeta=this->at(var->first);
    //              }
    //              catch ( exception &e ) {
    //                  currBasicVarExisting = false;
    //              };
    //              currBasicBeta = currBasicBeta + tab.getEntry(var->first, nonbasic).second * updateVal;
    //              this->at(var->first) = currBasicBeta;
    //          } else {
    //              string output;
    //              ostringstream stream1;
    //              ostringstream stream2;
    //              stream1 << var->first;
    //              output += stream1.str();
    //              output += ", ";
    //              stream2 << nonbasic;
    //              output += stream2.str();
    //              cout << "Beta value update not possible! \n There exists no constraint for the pair (basic, nonbasic) = (" << output << ") in the current Simplex Tableaux. \n Abort. \n";
    //          }
    //
    //      }
    //
    //  }
    //
    //=======
    //>>>>>>> .r110

}
