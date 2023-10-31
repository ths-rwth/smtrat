#pragma once

#include "../QEQuery.h"
#include <smtrat-common/smtrat-common.h>
#include "../util/VariableIndex.h"
#include "../util/Matrix.h"
#include "../util/EqualitySubstitution.h"
#include "Node.h"
#include "FMplexQEStatistics.h"

namespace smtrat::qe::fmplex {

class FMplexQE {

public: // type definitions
    using Matrix = qe::util::Matrix;
    using RowIndex = Matrix::RowIndex;
    using ColIndex = Matrix::ColIndex;
    using Row = std::vector<Matrix::RowEntry>;
   
private: // members
    QEQuery                 m_query;
    FormulaT                m_formula;
    std::vector<Node>       m_nodes;
    FormulaSetT             m_found_conjuncts;
    qe::util::VariableIndex m_var_idx;
    ColIndex                m_first_parameter_col;


public:

    FMplexQE(const FormulaT& qfree, const QEQuery& quantifiers)
    : m_query(quantifiers)
    , m_formula(qfree) {
        assert(
            qfree.type() == carl::FormulaType::CONSTRAINT ||
            qfree.is_real_constraint_conjunction()
        );
    }

    FormulaT eliminate_quantifiers();

private:
    std::vector<carl::Variable> gather_elimination_variables() const;

    ColIndex constant_column() const { return m_var_idx.size(); }
    ColIndex delta_column()    const { return constant_column() + 1; }
    ColIndex origin_column(RowIndex row) const { return delta_column() + 1 + row; }

    bool is_trivial(const Row& row) const {
        assert(!row.empty());
        return row.begin()->col_index >= constant_column();
    }


    bool is_global_conflict(const Row& row) const {
        assert(!row.empty());
        assert(is_trivial(row));
        auto it = row.begin();
        if (it->col_index > delta_column()) return false;
        if (it->col_index == constant_column()) {
            if (it->value < 0) return false;
            ++it;
            if (it->col_index == delta_column()) ++it; 
        }
        return std::all_of(it, row.end(), [](const auto& e){return e.value > 0;});
    }

    FormulaT constraint_from_row(const Row& row) const;
    bool is_positive_combination(const Row& row);

    /**
     * Constructs the starting node from m_query and m_formula as follows:
     * - Collects the variables in m_query and constraints in m_formula
     * - Uses equations in m_formula to eliminate as many variables as possible
     * - Filters finished constraints from the result
     * - Builds a matrix from the remaining constraints using build_initial_matrix
     * - The initial node contains that matrix and the remaining variables.
    */
    Node build_initial_system();

    /**
     * Constructs a matrix from the given constraints.
     * Each row of the matrix has the form [a_1 ... a_n | a'_1 ... a'_k| b | d | 0 ... 1 ... 0] where
     * The corresponding constraint is equivalent to 
     *     (a_1 x_1 + ... + a_n x_n) + (a'_1 y_1 + ... a'_k y_k) + (b + delta*d) <= 0,
     * x_1,...x_n are the quantified variables, y_1,...,y_k are the parameter variables,
     * d is 0 if the constraint is weak and 1 if it is strict,
     * the 0 ... 1 ... 0 part has one entry for each constraint, where the 1 indidicates at which
     *     index in the input constraints the corresponding constraint is.
    */
    Matrix build_initial_matrix(const FormulasT& constraints);

    /**
     * Eliminates the chosen column in parent by dropping all rows with non-zero entry in that column.
     * Should only be applied if the type of parent is NBS, i.e. if the chosen column is unbounded.
    */
    Node unbounded_elimination(Node& parent);

    /**
     * Eliminates the chosen column in parent using the next eliminator in parent.
     * This eliminator is then erased and added to the ignored rows.
     * Should only be applied if the type of parent is LBS or UBS.
    */
    Node bounded_elimination(Node& parent);

    /**
     * Eliminates the chosen column in parent using Fourier-Motzkin, but discards rows with 0 coeff.
     * Should only be called if type of parent is FM, i.e. if only one variable is left to eliminate.
    */
    Node fm_elimination(Node& parent);

    /**
     * Computes the next child using different elimination methods depending on the type of parent.
    */
    Node compute_next_child(Node& parent);
};

} // namespace smtrat::qe::fmplex