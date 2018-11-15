#pragma once
#include "../../../Common.h"

namespace smtrat::qe::fm{

/**
 * @brief Provides a simple implementation for Fourier Motzkin variable elimination for linear, existentially quantified constraints.
 *
 */
class FourierMotzkinQE {
private:
    QEQuery mQuery;
    FormulaT mFormula;
public:

    // a vector of iterators on single bounds
    using boundIteratorVector = std::vector<FormulaT::const_iterator>;
    // a pair of vectors containing sets of iterators to lower, respectively upper bounds.
    using boundIteratorPair = std::pair<boundIteratorVector, boundIteratorVector>;

    FourierMotzkinQE(const FormulaT& qfree, const QEQuery& quantifiers)
        : mQuery(quantifiers)
        , mFormula(qfree)
    {
        assert(qfree.type() == FormulaType::CONSTRAINT || qfree.isRealConstraintConjunction());
    }

    FormulaT eliminateQuantifiers();

private:
    boundIteratorPair findBounds(const carl::Variable& variable);

    std::vector<ConstraintT> createNewConstraints(const boundIteratorPair& bounds, carl::Variable v);

    void removeOldConstraints(const boundIteratorPair& bounds);

    bool isLinearLowerBound(const ConstraintT& f, carl::Variable v);
};

} // smtrat
