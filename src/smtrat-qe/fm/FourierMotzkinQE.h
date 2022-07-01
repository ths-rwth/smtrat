#pragma once

#include "../QEQuery.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat::qe::fm{

/**
 * @brief Provides a simple implementation for Fourier Motzkin variable elimination for linear, existentially quantified constraints.
 *
 */
class FourierMotzkinQE {
public:
    // we use four vectors, one for the discovered lower bounds, one for the upper bounds, one for the equations and one for unrelated constraints.
    using FormulaPartition = std::vector<std::vector<FormulaT>>;

private:
    QEQuery mQuery;
    FormulaT mFormula;
public:

    FourierMotzkinQE(const FormulaT& qfree, const QEQuery& quantifiers)
        : mQuery(quantifiers)
        , mFormula(qfree)
    {
        assert(qfree.type() == carl::FormulaType::CONSTRAINT || qfree.is_real_constraint_conjunction());
    }

    FormulaT eliminateQuantifiers();

private:
    FormulaPartition findBounds(const carl::Variable& variable);

    FormulasT createNewConstraints(const FormulaPartition& bounds, carl::Variable v);

    FormulasT substituteEquations(const FormulaPartition& bounds, carl::Variable v);

    bool isLinearLowerBound(const ConstraintT& f, carl::Variable v);

    Poly getRemainder(const ConstraintT& c, carl::Variable v, bool isLowerBnd);
};

} // smtrat
