#pragma once

#include "../QEQuery.h"

#include <smtrat-common/smtrat-common.h>

#include <eigen3/Eigen/Core>
#include <eigen3/Eigen/Dense>
#include <eigen3/Eigen/StdVector>

#include "../fmplex/FMplexQEStatistics.h"
#include "../util/VariableIndex.h"


namespace smtrat::qe::fm {

using vector_t = Eigen::Matrix<Rational, Eigen::Dynamic, 1>;
using matrix_t = Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic>;


class FourierMotzkinQE {
public:
    // we use four vectors: lower bounds, upper bounds, equations, unrelated constraints.
    using FormulaPartition = std::vector<FormulasT>;

private:
    QEQuery m_query;    /// The quantifiers to eliminate
    FormulaT m_formula; /// The logical representation of the solution space
    qe::util::VariableIndex m_var_idx;
    FormulaSetT m_finished;

public:
    FourierMotzkinQE(const FormulaT &qfree, const QEQuery &quantifiers)
            : m_query(quantifiers), m_formula(qfree) {

        assert(
            qfree.type() == carl::FormulaType::CONSTRAINT ||
            qfree.is_real_constraint_conjunction()
        );
    }

    FormulaT eliminateQuantifiers();

private:

    std::pair<matrix_t, vector_t> eliminateCol(const matrix_t& constraints,
                                               const vector_t& constants,
                                               std::size_t col,
                                               bool conservative = true);

    std::pair<matrix_t, vector_t> eliminateCols(const matrix_t &constraints,
                                                const vector_t constants,
                                                const std::vector<std::size_t> &cols,
                                                bool conservative = true);
};

} // smtrat
