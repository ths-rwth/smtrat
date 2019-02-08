#include <boost/test/unit_test.hpp>

#include <smtrat-modules/SATModule/SATModule.h>
#include <smtrat-common/smtrat-common.h>

using namespace smtrat;

BOOST_AUTO_TEST_SUITE(Test_SATModule);

BOOST_AUTO_TEST_CASE(Test_Simple)
{
	
	//carl::Variable x = carl::freshRealVariable("x");
	//carl::Variable b = carl::freshBooleanVariable("b");
	//
	//FormulaT c1(x + Rational(1), carl::Relation::LESS);
	//FormulaT c2(x - Rational(1), carl::Relation::GREATER);
	//
	//FormulaT clause1(carl::FormulaType::OR, {FormulaT(b), c1});
	//FormulaT clause2(carl::FormulaType::OR, {FormulaT(carl::FormulaType::NOT, FormulaT(b)), c2});
	//
	//auto input = std::make_unique<ModuleInput>();
	//auto conditions = std::vector<std::atomic_bool*>(1, new std::atomic_bool(false));
	//SATModule<SATSettingsMCSAT> sat(input.get(), conditions);
	//
	//sat.addCore(input->add(clause1).first);
	//sat.addCore(input->add(clause2).first);
	//sat.checkCore();
}

BOOST_AUTO_TEST_SUITE_END();
