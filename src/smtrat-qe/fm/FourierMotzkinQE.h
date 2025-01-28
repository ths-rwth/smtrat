#pragma once

#include "../QEQuery.h"

#include <smtrat-common/smtrat-common.h>

#include <eigen3/Eigen/Core>
#include <eigen3/Eigen/Dense>
#include <eigen3/Eigen/StdVector>

#include "FMQEStatistics.h"
#include "../util/VariableIndex.h"
#include "../util/Matrix.h"
#include "../util/redundancies.h"
#include "../util/EqualitySubstitution.h"
#include "../fmplex/Node.h"

namespace smtrat::qe::fm {

using vector_t = Eigen::Matrix<Rational, Eigen::Dynamic, 1>;
using matrix_t = Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic>;
using Matrix = qe::util::Matrix;
using RowIndex = Matrix::RowIndex;
using ColIndex = Matrix::ColIndex;
using Row = std::vector<Matrix::RowEntry>;
using Node = fmplex::Node;

class FourierMotzkinQE {
private:
    QEQuery                 m_query;
    FormulaT                m_formula;
    qe::util::VariableIndex m_var_idx;
    std::vector<Row>        m_found_rows;
    Matrix                  m_matrix;
    std::size_t             m_first_parameter_col;

public:
    FourierMotzkinQE(const FormulaT &qfree, const QEQuery &quantifiers)
    : m_query(quantifiers)
    , m_formula(qfree) {
        assert(
            qfree.type() == carl::FormulaType::CONSTRAINT ||
            qfree.is_real_constraint_conjunction()
        );
    }

    FormulaT eliminateQuantifiers();

private:

    ColIndex constant_column() const { return m_var_idx.size(); }
    ColIndex delta_column()    const { return constant_column() + 1; }

    bool is_trivial(const Row& row) const {
        return row.empty() || (row.begin()->col_index >= constant_column());
    }

    bool is_conflict(const Row& row) const {
        assert(is_trivial(row));
        return ((row.front().col_index <= delta_column()) && (row.front().value > 0));
    }

    void collect_constraint(const Row& row) {
        // check for redundancy
        for (auto it_other = m_found_rows.begin(); it_other != m_found_rows.end(); ++it_other) {
            auto red = util::compare_rows(*it_other, row, constant_column());
            if (red == util::Redundancy::FIRST_IMPLIES_SECOND) return;
            if (red == util::Redundancy::SECOND_IMPLIES_FIRST) { // overwrite the weaker constraint
                *it_other = row;
                return;
            }
        }
        m_found_rows.push_back(row);
    }


    std::vector<carl::Variable> gather_elimination_variables() const {
        std::vector<carl::Variable> elimination_vars;
        for (const auto& [type, vars] : m_query) {
            assert(type == QuantifierType::EXISTS); // Only support existential for now
            elimination_vars.insert(elimination_vars.end(), vars.begin(), vars.end());
        }
        return elimination_vars;
    }


    Matrix build_initial_matrix(const FormulasT& constraints) {
        // reserve enough space for the matrix
        Matrix m(constraints.size(), m_var_idx.size() + 2); // +2 : delta & rhs.
        std::size_t non_zeros = 2*constraints.size(); // one origin & at most one delta for each row
        for (const auto& f : constraints) non_zeros += f.constraint().lhs().nr_terms();
        m.reserve(non_zeros);

        // transform each constraint into a row
        for (RowIndex r = 0; r < constraints.size(); ++r) {
            carl::Relation rel = constraints[r].constraint().relation();

            // smtrat automatically converts constraints to < or <=
            assert(rel != carl::Relation::GREATER && rel != carl::Relation::GEQ);
            assert(rel != carl::Relation::NEQ); // we don't support NEQ yet

            Poly lhs = constraints[r].constraint().lhs();
            Rational constant_part = lhs.constant_part();
            lhs -= constant_part;

            Row entries;
            for (const auto& term : lhs) {
                entries.emplace_back(m_var_idx.index(term.single_variable()), term.coeff());
            }
            // the order in the polynomial may be different from the order in the var index
            std::sort(entries.begin(), entries.end(),
                [](const auto& lhs, const auto& rhs){ return lhs.col_index < rhs.col_index; }
            );

            // constant part, delta, and origin
            if (!carl::is_zero(constant_part)) entries.emplace_back(constant_column(), constant_part);
            if (rel == carl::Relation::LESS)   entries.emplace_back(delta_column(), Rational(1));

            if (entries.front().col_index >= m_first_parameter_col){
                collect_constraint(entries);
                if (rel == carl::Relation::EQ) {
                    for (auto& entry: entries) {
                        entry.value = -entry.value;
                    }
                    collect_constraint(entries);
                }
            }

            m.append_row(entries.begin(), entries.end());
        }
        return m;
    }


    FormulaT constraint_from_row(const Row& row) const {
        assert(!row.empty());
        assert(row.back().col_index <= delta_column());
        Poly lhs;
        auto it = row.begin();
        for (; it != row.end() && it->col_index < constant_column(); ++it) {
            lhs += it->value*Poly(m_var_idx.var(it->col_index));
        }
        if (it != row.end() && it->col_index == constant_column()) {
            lhs += it->value;
            ++it;
        }
        // This method is only applied to pos.lin. combinations, so the delta coeff will be >=0
        if (it != row.end() && it->col_index == delta_column()) {
            return FormulaT(lhs, carl::Relation::LESS);
        }
        return FormulaT(lhs, carl::Relation::LEQ);
    }


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
