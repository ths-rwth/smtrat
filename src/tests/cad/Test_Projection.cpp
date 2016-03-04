#include <boost/test/unit_test.hpp>

#include <iostream>

#include "../../lib/datastructures/cad/projection/Projection.h"
#include "../../lib/datastructures/cad/lifting/Sample.h"
#include "../../lib/modules/NewCADModule/NewCADSettings.h"
#include "../../lib/datastructures/cad/CAD.h"

using namespace smtrat;
using namespace smtrat::cad;

BOOST_AUTO_TEST_SUITE(Test_Projection);

BOOST_AUTO_TEST_CASE(Test_Projection_NO)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	Poly p = Poly(x*y)+Poly(y)+Rational(1);
	Poly q = Poly(y*y*y)+Poly(x*x*y)+Rational(2);
	
	ProjectionT<NewCADSettings1> projection;
	projection.reset({x,y});
	projection.addPolynomial(p.toUnivariatePolynomial(x));
	projection.addPolynomial(q.toUnivariatePolynomial(x));
	std::cout << projection << std::endl;
	
	Sample s(RAN(1));
	while (OptionalPoly op = projection.getPolyForLifting(1, s.liftedWith())) {
		std::cout << *op << std::endl;
	}

	CAD<NewCADSettings1> cad;
	cad.reset({x,y});
	cad.addConstraint(ConstraintT(p, carl::Relation::GEQ));
	cad.addConstraint(ConstraintT(q, carl::Relation::LEQ));
	cad.check();
}

BOOST_AUTO_TEST_CASE(Test_CAD)
{
	carl::Variable x = carl::freshRealVariable("x");
	carl::Variable y = carl::freshRealVariable("y");
	Poly p = Poly(x*y)+Poly(y)+Rational(1);
	Poly q = Poly(y*y*y)+Poly(x*x*y)+Rational(2);
	
	CAD<NewCADSettings1> cad;
	cad.reset({x,y});
	cad.addConstraint(ConstraintT(p, carl::Relation::GEQ));
	cad.addConstraint(ConstraintT(q, carl::Relation::LEQ));
	cad.check();
}

BOOST_AUTO_TEST_SUITE_END();
