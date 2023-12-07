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
    std::set<Row, cmp_row>  m_found_rows;


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

    bool is_conflict(const Row& row) const {
        assert(!row.empty());
        assert(is_trivial(row));
        const auto& e = row.front();
        return ((e.col_index <= delta_column()) && (e.value > 0));
    }

    FormulaT constraint_from_row(const Row& row) const;
    bool is_positive_combination(const Row& row);

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


    std::vector<Node> split_into_independent_nodes(const Node& n) const {
        const Matrix& m = n.matrix;
        std::vector<bool> col_used(n.cols_to_elim.size(), false);
        std::vector<bool> row_used(m.n_rows(), false);
        std::size_t n_unused_rows = m.n_rows();
        
        std::vector<std::size_t> pending;
        std::vector<Node> result;

        for (std::size_t i = 0; i < n.cols_to_elim.size();) {
            pending.push_back(i);
            result.push_back(Node(Matrix(n_unused_rows, m.n_cols()), {}));
            ++i;
            while (!pending.empty()) {
                std::size_t v = pending.back();
                pending.pop_back();
                if (col_used[v]) continue;
                col_used[v] = true;
                ColIndex actual_col = n.cols_to_elim[v];
                result.back().cols_to_elim.push_back(actual_col);
                auto col_end = m.col_end(actual_col);
                for (auto it = m.col_begin(actual_col); it != col_end; ++it) {
                    if (row_used[it.row()]) continue;
                    for (const auto& e : m.row_entries(it.row())) {
                        if (e.col_index >= m_first_parameter_col) break;
                        if (e.col_index == actual_col) continue;
                        for (std::size_t j = 0; ; ++j) {
                            assert(j < n.cols_to_elim.size());
                            if (n.cols_to_elim[j] == e.col_index) {
                                pending.push_back(j);
                                break;
                            }
                        }
                    }
                    row_used[it.row()] = true;
                    --n_unused_rows;
                    result.back().matrix.append_row(m.row_begin(it.row()), m.row_end(it.row()));
                    if (n.ignored.contains(it.row())) {
                        result.back().ignored.insert(result.back().matrix.n_rows());
                    }
                }
            }
            while (i < n.cols_to_elim.size() && col_used[i]) ++i;
        }
        for (Node& n : result) n.choose_elimination();
        return result;
    }


    /**
     * writes the given qe problem as a .ine file as used in CDD lib.
    */
    void write_matrix_to_ine(const Matrix& m, const std::string& filename) const;
    void write_matrix_to_redlog(const Matrix& m, const std::string& filename) const;
};

} // namespace smtrat::qe::fmplex