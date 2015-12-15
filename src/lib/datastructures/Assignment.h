/**
 * @file Assignment.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2014-01-14
 * @version 2014-10-27

 */

#pragma once

#include "../Common.h"
#include <map>
#include "../config.h"
#ifdef __VS
#pragma warning(push, 0)
#include <boost/variant.hpp>
#pragma warning(pop)
#else
#include <boost/variant.hpp>
#endif
#include <carl/core/RealAlgebraicNumber.h>
#include "vs/SqrtEx.h"
#include "SortValue.h"
#include "UFModel.h"
#include "model/Model.h"

namespace smtrat
{
    
    /**
     * Obtains all assignments which can be transformed to rationals and stores them in the passed map.
     * @param _model The model from which to obtain the rational assignments.
     * @param _rationalAssigns The map to store the rational assignments in.
     * @return true, if the entire model could be transformed to rational assignments. (not possible if, e.g., sqrt is contained)
     */
    bool getRationalAssignmentsFromModel( const Model& _model, EvalRationalMap& _rationalAssigns );
            
    /**
     * @param _assignment The assignment for which to check whether the given formula is satisfied by it.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _assignment, const FormulaT& _formula );
    
    bool isPartOf( const EvalRationalMap& _assignment, const Model& _model );
    
    /**
     * @param _model The assignment for which to check whether the given formula is satisfied by it.
     * @param _assignment The map to store the rational assignments in.
     * @param _formula The formula to be satisfied.
     * @return 0, if this formula is violated by the given assignment;
     *         1, if this formula is satisfied by the given assignment;
     *         2, otherwise.
     */
    unsigned satisfies( const Model& _model, const EvalRationalMap& _assignment, const std::map<carl::BVVariable, carl::BVTerm>& bvAssigns, const FormulaT& _formula );
    
    void getDefaultModel( Model& _defaultModel, const carl::UEquality& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const carl::BVTerm& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const ConstraintT& _constraint, bool _overwrite = true, size_t _seed = 0 );
    void getDefaultModel( Model& _defaultModel, const FormulaT& _formula, bool _overwrite = true, size_t _seed = 0 );
    
    std::ostream& operator<<( std::ostream& _out, const Model& _model );
}
