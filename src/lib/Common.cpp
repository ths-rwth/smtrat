/**
 * Common.cpp
 * @author Florian Corzilius
 * @since 2015-08-27
 * @version 2015-08-27
 */

#include "Common.h"

using carl::Term;
using carl::MultivariatePolynomial;
using carl::Constraint;
using carl::Formula;
using carl::Interval;

template class carl::Term<smtrat::Rational>;
template class carl::MultivariatePolynomial<smtrat::Rational>;
template class carl::Constraint<smtrat::Poly>;
template class carl::Formula<smtrat::Poly>;
template class carl::Interval<smtrat::Rational>;
template class carl::Interval<double>;
template struct carl::VariableInformation<true, smtrat::Poly>;

//template class std::set<carl::Constraint<smtrat::Poly>, carl::less<carl::Constraint<smtrat::Poly>, false>>;
//template class std::vector<carl::Formula<smtrat::Poly>>;
//template class std::set<carl::Formula<smtrat::Poly>>;
//template class std::multiset<carl::Formula<smtrat::Poly>, carl::less<carl::Formula<smtrat::Poly>>>;
//template class std::map<carl::Variable,smtrat::Rational>;
//template class std::map<carl::Variable,smtrat::RationalInterval>;
//template class std::map<carl::Variable,smtrat::DoubleInterval>;
//template class std::map<carl::Variable, carl::VariableInformation<true, smtrat::Poly>>;
//template class std::map<smtrat::Poly,carl::exponent>;
