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
#include <carl/core/FactorizedPolynomial.h>
#include <carl/core/Variable.h>
#include <carl/core/VariablePool.h>
#include <carl/interval/Interval.h>
#include <carl/interval/IntervalEvaluation.h>
#include <carl/interval/Contraction.h>
#include <carl/io/streamingOperators.h>
#include <carl/util/Common.h>
#include <carl/formula/Logic.h>
#include <carl/formula/FormulaPool.h>
#include <carl/formula/uninterpreted/UFManager.h>
#include <carl/formula/uninterpreted/UFInstanceManager.h>
#include <carl/formula/model/Model.h>
#include <carl/formula/model/evaluation/ModelEvaluation.h>

#include "logging.h"

namespace smtrat
{
	using carl::operator<<;

  using Logic = carl::Logic;
  ///An enum with the possible answers a Module can give
  enum Answer { SAT = 0, UNSAT = 1, UNKNOWN = 2, ABORTED = 3 };
	inline std::ostream& operator<<(std::ostream& os, const Answer& a) {
		switch (a) {
			case Answer::SAT:		return os << "SAT";
			case Answer::UNSAT:		return os << "UNSAT";
			case Answer::UNKNOWN:	return os << "UNKNOWN";
			case Answer::ABORTED:	return os << "ABORTED";
		}
		return os << "???";
	}

  // An enum with the levels for lemma generation
  enum LemmaLevel { NONE = 0, NORMAL = 1, ADVANCED = 2 };

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
  using Rational = mpq_class; // Use always GMP as CLN does not work for rationalize

	typedef carl::IntegralType<Rational>::type Integer;

  typedef carl::Term<Rational> TermT;

  using Poly = carl::MultivariatePolynomial<Rational>;

  typedef carl::Constraint<Poly> ConstraintT;

  typedef carl::Constraints<Poly> ConstraintsT;
	
	typedef carl::MultivariateRoot<Poly> MultivariateRootT;
	
	typedef carl::VariableAssignment<Poly> VariableAssignmentT;
	
	typedef carl::VariableComparison<Poly> VariableComparisonT;
	
	typedef carl::PBConstraint<Poly> PBConstraintT;

  typedef carl::Formula<Poly> FormulaT;

  typedef carl::Formulas<Poly> FormulasT;

	typedef carl::FormulaSet<Poly> FormulaSetT;

	typedef carl::FormulasMulti<Poly> FormulasMultiT;

  typedef carl::EvaluationMap<Rational> EvalRationalMap;

  typedef carl::Interval<Rational> RationalInterval;

  typedef carl::EvaluationMap<RationalInterval> EvalRationalIntervalMap;

  typedef carl::Interval<double> DoubleInterval;

  typedef carl::EvaluationMap<DoubleInterval> EvalDoubleIntervalMap;

  typedef carl::VarInfo<Poly> VarPolyInfo;

  typedef carl::VarInfoMap<Poly> VarPolyInfoMap;
	
	using Model = carl::Model<Rational, Poly>;
	static const Model EMPTY_MODEL = Model();
	
	using ModelSubstitution = carl::ModelSubstitution<Rational, Poly>;
	
	using ModelMVRootSubstitution = carl::ModelMVRootSubstitution<Rational, Poly>;
	using ModelPolynomialSubstitution = carl::ModelPolynomialSubstitution<Rational, Poly>;
	
	using ModelVariable = carl::ModelVariable;
	
	using ModelValue = carl::ModelValue<Rational, Poly>;
	
	using InfinityValue = carl::InfinityValue;
	
	using SqrtEx = carl::SqrtEx<smtrat::Poly>;

  template<template<typename> class Operator>
  using Contractor = carl::Contraction<Operator, Poly>;

  typedef carl::Factors<Poly> Factorization;

#ifdef __VS
    typedef std::vector<std::atomic<bool>*> Conditionals;
#else
    typedef std::vector<std::atomic_bool*> Conditionals;
#endif

	// Pair of priority and module id (within the respective strategy graph)
    typedef std::pair<std::size_t, std::size_t> thread_priority;

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
    
    static const EvalDoubleIntervalMap EMPTY_EVAL_DOUBLE_INTERVAL_MAP = EvalDoubleIntervalMap();

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
