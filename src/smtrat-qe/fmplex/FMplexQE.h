#pragma once

#include "../QEQuery.h"
#include <smtrat-common/smtrat-common.h>
#include "../util/VariableIndex.h"
#include "../util/Matrix.h"
#include "../util/redundancies.h"
#include "../util/EqualitySubstitution.h"
#include "Node.h"
#include "FMplexQEStatistics.h"
#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SimplexModule/SimplexModule.h>


namespace smtrat::qe::fmplex {

class FMplexQE {

public: // type definitions
    using Matrix = qe::util::Matrix;
    using RowIndex = Matrix::RowIndex;
    using ColIndex = Matrix::ColIndex;
    using Row = std::vector<Matrix::RowEntry>;

    struct cmp_row {
        bool operator()(const Row& a, const Row& b) const {
            auto it_a = a.begin(), it_b = b.begin();
            auto end_a = a.end(), end_b = b.end();
            while (it_a != end_a && it_b != end_b) {
                if (it_a->col_index != it_b->col_index) 
                    return it_a->col_index < it_b->col_index;
                if (it_a->value != it_b->value)
                    return it_a->value < it_b->value;
                ++it_a;
                ++it_b;
            }
            return (it_b != end_b); // at this point: a < b only if a is at end and b is not
        }
    };
   
private: // members
    QEQuery                 m_query;
    FormulaT                m_formula;
    std::vector<Node>       m_nodes;
    FormulaSetT             m_found_conjuncts;
    qe::util::VariableIndex m_var_idx;
    ColIndex                m_first_parameter_col;
    std::vector<Row>        m_found_rows;


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

    bool is_conflict(const Row& row) const {
        assert(is_trivial(row));
        return ((row.front().col_index <= delta_column()) && (row.front().value > 0));
    }

    bool is_positive_combination(const Row& row);

    FormulaT constraint_from_row(const Row& row) const;

    /**
     * truncates the given row to not contain any "origin" information
     * and inserts the result into the set of final projected constraints-
     * This assumes that the row does contain origins and does not contain elimination variables.
    */
    void collect_constraint(const Row& row) {
        Row truncated = row;
        for (std::size_t i = 0; ; ++i) {
            if (truncated[i].col_index > delta_column()) {
                truncated.resize(i);
                break;
            }
        }

        // check for redundancy
        for (auto it_other = m_found_rows.begin(); it_other != m_found_rows.end(); ++it_other) {
            auto red = util::compare_rows(*it_other, truncated, constant_column());
            if (red == util::Redundancy::FIRST_IMPLIES_SECOND) return;
            if (red == util::Redundancy::SECOND_IMPLIES_FIRST) { // overwrite the weaker constraint
                *it_other = truncated;
                return;
            }
        }
        m_found_rows.push_back(truncated);
    }


    void remove_redundancies(Node& n) {
        FormulasT constraints;
        FormulasT result;
        const Matrix& m = n.matrix;
        Matrix result_m(m.n_rows(), m.n_cols());
        carl::Variable delta = carl::fresh_real_variable("delta");
        for (RowIndex i = 0; i < m.n_rows(); ++i) {
            Poly lhs;
            auto it = m.row_begin(i);
            const auto end = m.row_end(i);
            for (; it != end && it->col_index < constant_column(); ++it) {
                lhs += it->value*Poly(m_var_idx.var(it->col_index));
            }
            if (it != end && it->col_index == constant_column()) {
                lhs += it->value;
                ++it;
            }
            if (it != end && it->col_index == delta_column()) {
                lhs += it->value*Poly(delta);
            }
            constraints.push_back(FormulaT(lhs, carl::Relation::LEQ));
        }

        auto irred_rows = util::irredundant_rows(constraints, {FormulaT(Poly(delta), carl::Relation::GREATER)});
        
        std::set<RowIndex> new_ignored;
        
        for (std::size_t i = 0; i < irred_rows.size(); ++i) {
            result_m.append_row(m.row_begin(irred_rows[i]), m.row_end(irred_rows[i]));
            if (n.ignored.contains(irred_rows[i])) {
                new_ignored.emplace_hint(new_ignored.end(), i);
            }
        }

        n.matrix = result_m;
        n.ignored = new_ignored;
    }

    /**
     * Splits the given node into multiple nodes that are independent in the following sense:
     * - they partition the elimination variables and
     * - the constraints of a node to not contain any of the elimination variables of another node.
     * Thus, these eliminations can be carried out independently.
    */
    std::vector<Node> split_into_independent_nodes(const Node& n) const;

    /**
     * Constructs the starting nodes from m_query and m_formula as follows:
     * - Collects the variables in m_query and constraints in m_formula
     * - Uses equations in m_formula to eliminate as many variables as possible
     * - Filters finished constraints from the result
     * - Splits the variables and constraints into independent blocks
     * - Builds a matrix for each block using build_initial_matrix
     * - Adds an according Node for each block to the stack of nodes
    */
    void build_initial_systems();

    /**
     * Constructs a matrix from the given constraints.
     * Each row of the matrix has the form [a_1 ... a_n | a'_1 ... a'_k| b | d | 0 ... 1 ... 0] where
     * - The corresponding constraint is equivalent to 
     *     (a_1 x_1 + ... + a_n x_n) + (a'_1 y_1 + ... a'_k y_k) + (b + delta*d) <= 0,
     * - x_1,...x_n are the quantified variables, y_1,...,y_k are the parameter variables,
     * - d is 0 if the constraint is weak and 1 if it is strict,
     * - the 0 ... 1 ... 0 part has one entry for each constraint, where the 1 indidicates at which
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
     * @return false if a global conflict is found and true otherwise.
    */
    bool fm_elimination(Node& parent);

    /**
     * writes the given qe problem as a .ine file as used in CDD lib.
    */
    void write_matrix_to_ine(const Matrix& m, const std::string& filename) const;
    void write_matrix_to_redlog(const Matrix& m, const std::string& filename) const;
};

} // namespace smtrat::qe::fmplex