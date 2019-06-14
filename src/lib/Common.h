#pragma once

/**
 * @file
 * Provide useful type aliases, especially for the performance 
 * critical underlying coefficient types of polynomials, as well as 
 * enums and constants.
 */
 
#include <vector>
#include <set>
#include <string.h>
#include <unordered_set>
#include <unordered_map>
#include <atomic>

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl/core/VariablePool.h>
#include <carl/interval/Interval.h>
#include <carl/interval/IntervalEvaluation.h>
#include <carl/util/Common.h>
#include <carl/formula/Logic.h>
#include <carl/formula/FormulaPool.h>
#include <carl/formula/uninterpreted/UFManager.h>
#include <carl/formula/uninterpreted/UFInstanceManager.h>
#include <carl-model/Model.h>
#include <carl-model/evaluation/ModelEvaluation.h>

#include <smtrat-common/smtrat-common.h>

namespace smtrat
{

  using Logic = carl::Logic;

    // Further type definitions.
/*#ifdef SMTRAT_STRAT_PARALLEL_MODE
    typedef mpq_class Rational;
#else
#ifdef USE_GINAC
    typedef cln::cl_RA Rational;
#else
    typedef mpq_class Rational;
#endif
#endif*/
//  using Rational = mpq_class; // Use always GMP as CLN does not work for rationalize

	typedef carl::IntegralType<Rational>::type Integer;

  typedef carl::Term<Rational> TermT;

//  using Poly = carl::MultivariatePolynomial<Rational>;

  template<typename Coeff> using UPoly = carl::UnivariatePolynomial<Coeff>;

  using RANPoint = carl::RealAlgebraicPoint<Rational>;

//  typedef carl::Constraint<Poly> ConstraintT;
//
//  typedef carl::Constraints<Poly> ConstraintsT;
	
	using MultivariateRootT = carl::MultivariateRoot<Poly>;
	using RootExpr = carl::MultivariateRoot<Poly>; // prefer this one

//  typedef carl::Formula<Poly> FormulaT;

//  typedef carl::Formulas<Poly> FormulasT;

  typedef carl::VarInfoMap<Poly> VarPolyInfoMap;
	
	using ModelMVRootSubstitution = carl::ModelMVRootSubstitution<Rational, Poly>;
	
	using SqrtEx = carl::SqrtEx<smtrat::Poly>;

//#ifdef __VS
//    typedef std::vector<std::atomic<bool>*> Conditionals;
//#else
//    typedef std::vector<std::atomic_bool*> Conditionals;
//#endif


    // Constants.
    ///@todo move static variables to own cpp
    static const Rational ZERO_RATIONAL = Rational( 0 );

    static const Rational ONE_RATIONAL = Rational( 1 );

    static const Rational MINUS_ONE_RATIONAL = Rational( -1 );

    static const Poly ZERO_POLYNOMIAL = Poly( ZERO_RATIONAL );

    static const Poly ONE_POLYNOMIAL = Poly( ONE_RATIONAL );

    static const Poly MINUS_ONE_POLYNOMIAL = Poly( MINUS_ONE_RATIONAL );

    static const unsigned MAX_DEGREE_FOR_FACTORIZATION = 6;

    static const unsigned MIN_DEGREE_FOR_FACTORIZATION = 2;

    static const unsigned MAX_DIMENSION_FOR_FACTORIZATION = 6;

    static const unsigned MAX_NUMBER_OF_MONOMIALS_FOR_FACTORIZATION = 7;

}    // namespace smtrat

extern template class carl::Term<smtrat::Rational>;
extern template class carl::MultivariatePolynomial<smtrat::Rational>;
extern template class carl::Constraint<smtrat::Poly>;
extern template class carl::Formula<smtrat::Poly>;
extern template class carl::Interval<smtrat::Rational>;
extern template class carl::Interval<double>;
extern template struct carl::VariableInformation<true, smtrat::Poly>;

//extern template class std::set<carl::Constraint<smtrat::Poly>, carl::less<carl::Constraint<smtrat::Poly>, false>>;
//extern template class std::vector<carl::Formula<smtrat::Poly>>;
//extern template class std::set<carl::Formula<smtrat::Poly>>;
//extern template class std::multiset<carl::Formula<smtrat::Poly>, carl::less<carl::Formula<smtrat::Poly>>>;
//extern template class std::map<carl::Variable,smtrat::Rational>;
//extern template class std::map<carl::Variable,smtrat::RationalInterval>;
//extern template class std::map<carl::Variable,smtrat::DoubleInterval>;
//extern template class std::map<carl::Variable, carl::VariableInformation<true, smtrat::Poly>>;
//extern template class std::map<smtrat::Poly,carl::exponent>;
