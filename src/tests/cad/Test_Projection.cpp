#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/cad/projection/Projection.h"
#include "../../lib/datastructures/cad/lifting/Sample.h"
// #include "../../lib/datastructures/cad/debug/Projection.h"
#include "../../lib/modules/NewCADModule/NewCADSettings.h"
#include "../../lib/datastructures/cad/CAD.h"

using namespace smtrat;
using namespace smtrat::cad;

BOOST_AUTO_TEST_SUITE(Test_Projection);

// BOOST_AUTO_TEST_CASE(Projection)
// {
// 	carl::Variable x = carl::freshRealVariable("x");
// 	carl::Variable y = carl::freshRealVariable("y");
// 	
// 	debug::Projection p({x,y});
// 	
// 	p.add(ConstraintT(Poly(x) + Poly(y), carl::Relation::LEQ));
// 	p.add(ConstraintT(Poly(y), carl::Relation::GREATER));
// 	p.add(ConstraintT(Poly(x) + Poly(1), carl::Relation::GREATER));
// 	
// 	std::cout << p.getProjection() << std::endl;
// 	
// 	
// 	
// 	//ProjectionT<NewCADSettingsSO> projection;
// 	//projection.reset({x,y});
// 	//projection.addPolynomial(p.toUnivariatePolynomial(x), 0);
// 	//projection.addPolynomial(q.toUnivariatePolynomial(x), 1);
// 	//std::cout << projection << std::endl;
// 	//
// 	//Sample s(RAN(1));
// 	//while (auto pid = projection.getPolyForLifting(1, s.liftedWith())) {
// 	//	std::cout << projection.getPolynomialById(1, *pid) << std::endl;
// 	//}
// }
// 
// BOOST_AUTO_TEST_CASE(Test_CAD)
// {
// 	carl::Variable x = carl::freshRealVariable("x");
// 	carl::Variable y = carl::freshRealVariable("y");
// 	Poly p = Poly(x*y)+Poly(y)+Rational(1);
// 	Poly q = Poly(y*y*y)+Poly(x*x*y)+Rational(2);
// 	
// 	CAD<NewCADSettingsSO> cad;
// 	cad.reset({x,y});
// 	cad.addConstraint(ConstraintT(p, carl::Relation::GEQ));
// 	cad.addConstraint(ConstraintT(q, carl::Relation::LEQ));
// 	
// 	Assignment a;
// 	std::vector<FormulaSetT> mis;
// 	cad.check(a, mis);
// }

BOOST_AUTO_TEST_SUITE_END();
