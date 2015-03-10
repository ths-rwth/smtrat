/**
 * @file Common.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

//#define STANDALONE
#ifdef STANDALONE
#include <carl/numbers/numbers.h>
#include <carl/core/MultivariatePolynomial.h>
#include <carl/formula/UVariable.h>
#include <carl/formula/UFInstance.h>
#include <carl/formula/UFInstanceManager.h>
#include <carl/formula/UninterpretedFunction.h>
#include <carl/formula/UFManager.h>
#include <carl/formula/Formula.h>
#include <carl/formula/FormulaPool.h>
#include <carl/formula/bitvector/BVTerm.h>
#include <carl/formula/bitvector/BVTermPool.h>
namespace smtrat {
	enum class Logic : unsigned { UNDEFINED, QF_NRA, QF_LRA, QF_NIA, QF_LIA };
	typedef cln::cl_RA Rational;
	typedef carl::MultivariatePolynomial<Rational> Poly;
	typedef carl::Constraint<Poly> ConstraintT;
	typedef carl::Formula<Poly> FormulaT;
}
#include "ParserTypes.h"
namespace smtrat {
    inline void annotateFormula( const FormulaT&, const vector<parser::Attribute>& )
    {
    }
}
#define SMTRAT_LOG_ERROR(...)
#else
#include "../../lib/Common.h"
#include "../../lib/solver/ModuleInput.h"
#endif