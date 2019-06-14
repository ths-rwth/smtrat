#define BOOST_TEST_MODULE test_onecellcadbug

#include <optional>

#include <boost/test/unit_test.hpp>

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include <carl/core/MultivariatePolynomial.h>
#include <carl/core/Variable.h>
#include <carl-model/evaluation/ModelEvaluation.h>

#include <smtrat-mcsat/explanations/onecellcad/Explanation.h>


using namespace smtrat;

BOOST_AUTO_TEST_CASE(OneCellCadBug) {
	// Variable x cannot be assigned for x^2 + x^4 + b*x^3 <= 0 , x != 0 under b -> -1
	
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable b = carl::freshRealVariable("b");
  carl::Variables vars({x,b});

	FormulaT f1(ConstraintT((Poly(x)*x) + (Poly(x)*x*x*x) + (Poly(b)*x*x*x), carl::Relation::LEQ));
  FormulaT f2(ConstraintT(x, carl::Relation::NEQ));

	// generate explanation
  mcsat::Bookkeeping bookkeeping;
  bookkeeping.updateVariables(vars);
  bookkeeping.pushConstraint(f1);
  bookkeeping.pushConstraint(f2);
  bookkeeping.pushAssignment(b, Rational(-1), FormulaT(carl::FormulaType::TRUE));
  ::smtrat::mcsat::onecellcad::Explanation expl;
  auto explanation = expl(bookkeeping, x, FormulasT({f1,f2}));


  // proof that satisfying assignment exist
  Model model;
	model.assign(b, Rational(-5));
  model.assign(x, Rational(1));

  auto res = carl::model::evaluate(f1, model);
	BOOST_CHECK(res.isBool() && res.asBool());
  auto res1 = carl::model::evaluate(f2, model);
	BOOST_CHECK(res1.isBool() && res1.asBool());

  auto res2 = carl::model::evaluate(boost::get<FormulaT>(*explanation), model);
  BOOST_CHECK(res2.isBool());
  BOOST_CHECK(res2.asBool());
}