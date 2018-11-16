#pragma once
#include "../../../Common.h"

namespace smtrat::qe::fm{

/**
 * @brief Provides a simple implementation for Fourier Motzkin variable elimination for linear, existentially quantified constraints.
 *
 */
class FourierMotzkinQE {
public:
    // we use three vectors, one for the discovered lower bounds, one for the upper bounds and one for unrelated constraints.
    using FormulaPartition = std::vector<std::vector<FormulaT::const_iterator>>;

private:
    QEQuery mQuery;
    FormulaT mFormula;
public:

    FourierMotzkinQE(const FormulaT& qfree, const QEQuery& quantifiers)
        : mQuery(quantifiers)
        , mFormula(qfree)
    {
        assert(qfree.getType() == carl::FormulaType::CONSTRAINT || qfree.isRealConstraintConjunction());
    }

    FormulaT eliminateQuantifiers();

private:
    FormulaPartition findBounds(const carl::Variable& variable);

    carl::Formulas<Poly> createNewConstraints(const FormulaPartition& bounds, carl::Variable v);

    bool isLinearLowerBound(const ConstraintT& f, carl::Variable v);
};

} // smtrat
