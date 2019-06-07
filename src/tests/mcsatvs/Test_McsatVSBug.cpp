#include <optional>

#include <boost/test/unit_test.hpp>

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include <carl/core/Variable.h>
#include <carl/formula/model/evaluation/ModelEvaluation.h>

#include <smtrat-mcsat/explanations/vs/VSHelper.h>


using namespace smtrat;

BOOST_AUTO_TEST_CASE(McsatVSBug) {
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
  carl::Variable z = carl::freshRealVariable("z");

  // 100 + -49*y^2 + -49*z^2 + 98*z*x + -98*x^2 < 0
  Poly p = Poly(Rational(100)) - Poly(Rational(49))*y*y - Poly(Rational(49))*z*z + Poly(Rational(98))*z*x - Poly(Rational(98))*x*x;
  ConstraintT c1(p, carl::Relation::LESS);

  // proof that f1 is false given a model
  Model m;
  m.assign(x, Rational(10)/7);
  m.assign(y, Rational(0));
  m.assign(z, Rational(10)/7);

  auto res = carl::model::evaluate(FormulaT(c1), m);
	BOOST_CHECK(res.isBool());
  BOOST_CHECK(!res.asBool());

  auto res2 = carl::model::evaluate(p, m);
	BOOST_CHECK(res2.isRational());
  BOOST_CHECK(res2.asRational() >= 0);

  // but VS returns true after substituting x -> 10/7 into c1
  ::vs::Substitution sub(x, SqrtEx(Poly(Rational(10)/7)), ::vs::Substitution::Type::NORMAL, carl::PointerSet<::vs::Condition>());
  smtrat::vs::DisjunctionOfConstraintConjunctions subResTmp;
  bool r = mcsat::vs::helper::substituteHelper(c1, sub, subResTmp);
  BOOST_CHECK(r);
  auto subRes = mcsat::vs::helper::doccToFormula(subResTmp);
  BOOST_CHECK(subRes.getType() != carl::FormulaType::TRUE);

  // The bug lies in splitSosDecompositions()
}