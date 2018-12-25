#include <boost/test/unit_test.hpp>

#include <iostream>

#include <smtrat-cad/CAD.h>
#include <smtrat-cad/projection/Projection.h>
#include <smtrat-cad/projection/Projection_Debug.h>
#include <smtrat-cad/lifting/Sample.h>
#include <smtrat-modules/NewCADModule/NewCADSettings.h>


using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_Projection);

BOOST_AUTO_TEST_CASE(Projection)
{
	carl::Variable a = carl::freshRealVariable("a");
	carl::Variable b = carl::freshRealVariable("b");
	carl::Variable c = carl::freshRealVariable("c");
	carl::Variable d = carl::freshRealVariable("d");
	carl::Variable e = carl::freshRealVariable("e");
	carl::Variable f = carl::freshRealVariable("f");
	carl::Variable g = carl::freshRealVariable("g");

	Poly p1 = Poly(b)*b - Poly(10)*c - Poly(1);
	Poly p2 = Poly(b);
	Poly p3 = Poly(d) - Poly(c);
	Poly p4 = Poly(b);
	Poly p5 = Poly(f);
	//Poly p6 = Poly(b);

	cad::projection::Projection_Debug<cad::ProjectionType::McCallum> projection("projection.dot", {e, g, c, d, f, b});
	projection.doProjection({p1, p2, p3, p4, p5});
}
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
