#define BOOST_TEST_MODULE test_fm

#include <boost/test/unit_test.hpp>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-qe/fm/qe.h>
#include <iostream>

using namespace smtrat;

BOOST_AUTO_TEST_SUITE( FMQE );

BOOST_AUTO_TEST_CASE( FMQE_eliminate_single_variable )
{
    carl::Variable x = carl::freshRealVariable("x");
    carl::Variable y = carl::freshRealVariable("y");
    carl::Variable z = carl::freshRealVariable("z");

    ConstraintT c1 = ConstraintT(Poly(x) - Poly(y) + Poly(z), carl::Relation::GEQ);
    ConstraintT c2 = ConstraintT(Poly(x) + Poly(y) + Poly(-5), carl::Relation::LEQ);

    FormulasT constraints;
    constraints.emplace_back(c1);
    constraints.emplace_back(c2);

    FormulaT inFormula = FormulaT(carl::FormulaType::AND, constraints);

    std::cout << "Formula: " << inFormula << ", eliminate " << x << std::endl;

    qe::QEQuery query;
    query.emplace_back(std::make_pair(qe::QuantifierType::EXISTS,std::vector<carl::Variable>{x}));

    auto newFormula = qe::fm::eliminateQuantifiers(inFormula, query);

    std::cout << "New formula: " << newFormula << std::endl;

    BOOST_TEST(true, "Ran successfully.");
}

BOOST_AUTO_TEST_CASE( FMQE_eliminate_to_true )
{
    carl::Variable x = carl::freshRealVariable("x");
    carl::Variable y = carl::freshRealVariable("y");

    ConstraintT c1 = ConstraintT(Poly(x) - Poly(y), carl::Relation::GEQ);
    ConstraintT c2 = ConstraintT(Poly(x) - Poly(y) + Poly(-5), carl::Relation::LEQ);

    FormulasT constraints;
    constraints.emplace_back(c1);
    constraints.emplace_back(c2);

    FormulaT inFormula = FormulaT(carl::FormulaType::AND, constraints);

    std::cout << "Formula: " << inFormula << ", eliminate " << x << std::endl;

    qe::QEQuery query;
    query.emplace_back(std::make_pair(qe::QuantifierType::EXISTS,std::vector<carl::Variable>{x}));

    auto newFormula = qe::fm::eliminateQuantifiers(inFormula, query);

    std::cout << "New formula: " << newFormula << std::endl;

    BOOST_TEST((newFormula == FormulaT(carl::FormulaType::TRUE)));
}

BOOST_AUTO_TEST_CASE( FMQE_eliminate_to_true_with_remaining_constraint )
{
    carl::Variable x = carl::freshRealVariable("x");
    carl::Variable y = carl::freshRealVariable("y");
    carl::Variable z = carl::freshRealVariable("z");

    ConstraintT c1 = ConstraintT(Poly(x) - Poly(y), carl::Relation::GEQ);
    ConstraintT c2 = ConstraintT(Poly(x) - Poly(y) + Poly(-5), carl::Relation::LEQ);
    ConstraintT c3 = ConstraintT(Poly(y) - Poly(z), carl::Relation::LEQ);

    FormulasT constraints;
    constraints.emplace_back(c1);
    constraints.emplace_back(c2);
    constraints.emplace_back(c3);

    FormulaT inFormula = FormulaT(carl::FormulaType::AND, constraints);

    std::cout << "Formula: " << inFormula << ", eliminate " << x << std::endl;

    qe::QEQuery query;
    query.emplace_back(std::make_pair(qe::QuantifierType::EXISTS,std::vector<carl::Variable>{x}));

    auto newFormula = qe::fm::eliminateQuantifiers(inFormula, query);

    std::cout << "New formula: " << newFormula << std::endl;

    BOOST_TEST((newFormula == FormulaT(c3)));
}

BOOST_AUTO_TEST_CASE( FMQE_eliminate_several_variables )
{
    carl::Variable x = carl::freshRealVariable("x");
    carl::Variable y = carl::freshRealVariable("y");
    carl::Variable z = carl::freshRealVariable("z");

    ConstraintT c1 = ConstraintT(Poly(x) - Poly(y) + Poly(z), carl::Relation::GEQ);
    ConstraintT c2 = ConstraintT(Poly(y), carl::Relation::GEQ);
    ConstraintT c3 = ConstraintT(Poly(x) + Poly(y) + Poly(-5), carl::Relation::LEQ);

    FormulasT constraints;
    constraints.emplace_back(c1);
    constraints.emplace_back(c2);
    constraints.emplace_back(c3);

    FormulaT inFormula = FormulaT(carl::FormulaType::AND, constraints);

    std::cout << "Formula: " << inFormula << std::endl;

    qe::QEQuery query;
    query.emplace_back(std::make_pair(qe::QuantifierType::EXISTS,std::vector<carl::Variable>{x,y}));

    auto newFormula = qe::fm::eliminateQuantifiers(inFormula, query);

    std::cout << "New formula: " << newFormula << std::endl;

    BOOST_TEST(true, "Ran successfully.");
}

BOOST_AUTO_TEST_SUITE_END();
