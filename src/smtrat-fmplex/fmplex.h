#pragma once

#include <vector>
#include <cassert>

#include "Matrix.h"
#include "Node.h"

namespace smtrat::fmplex {

// TODO: equality substitution
class FMplexElimination {

    using RowIndex = Matrix::RowIndex;
    using ColIndex = Matrix::ColIndex;
    using RowEntry = Matrix::RowEntry;
    using Row      = std::vector<RowEntry>;

    struct cmp_row {
        bool operator()(const Row& a, const Row& b) const { // TODO: this does not filter out duplicates with different lin. combs.!
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


private:
    std::vector<Node>       m_nodes;
    ColIndex                m_first_parameter_col;
    ColIndex                m_constant_col;
    ColIndex                m_total_cols;
    std::set<Row, cmp_row>  m_found_rows;

public:
    FMplexElimination(const Matrix& m, std::size_t n_quantified, std::size_t n_parameters) {
        m_first_parameter_col = n_quantified;
        m_constant_col = n_quantified + n_parameters;

        // filter finished rows from m
        // store initial Node
    }


    Matrix apply() {
        while (!m_nodes.empty()) {
            switch (m_nodes.back().type) {
            case Node::Type::CONFLICT:
                return trivial_unsat_matrix();
            case Node::Type::UNDETERMINED: {
                auto split = split_into_independent_nodes(m_nodes.back());
                m_nodes.pop_back();
                m_nodes.insert(m_nodes.end(), split.begin(), split.end());
                break;
            }
            case Node::Type::NBS:
                m_nodes.back() = unbounded_elimination(m_nodes.back());
                break;
            case Node::Type::LBS:[[fallthrough]];
            case Node::Type::UBS:
                if (m_nodes.back().is_finished()) m_nodes.pop_back();
                else m_nodes.push_back(bounded_elimination(m_nodes.back()));
                break;
            case Node::Type::FM:
                if (!fm_elimination(m_nodes.back())) return trivial_unsat_matrix();
                m_nodes.pop_back();
                break;
            case Node::Type::LEAF:
                m_nodes.pop_back();
                break;
            }
        }

        Matrix result(m_found_rows.size(), m_total_cols);
        for (const auto& r : m_found_rows) {
            result.append_row(r.begin(), r.end());
        }
        
        return result;
    }


private:
    ColIndex constant_column()             const { return m_constant_col; }
    ColIndex delta_column   ()             const { return m_constant_col + 1; }
    ColIndex origin_column  (RowIndex row) const { return delta_column() + 1 + row; }

    bool is_trivial(const Row& row) const {
        assert(!row.empty());
        return row.begin()->col_index >= constant_column();
    }

    bool is_conflict(const Row& row) const {
        assert(!row.empty());
        assert(is_trivial(row));
        const auto& e = row.front();
        return (e.col_index <= delta_column()) && (e.value > 0);
    }

    bool is_positive_combination(const Row& row) const {
        assert(row.front().col_index <= delta_column());
        // don't need to check for it == end because the constraint cannot be trivially true here
        for (auto it = row.rbegin(); it->col_index > delta_column(); ++it) {
            if (it->value < 0) return false;
        }
        return true;
    }

    bool is_global_conflict(const Row& row) const {
        return is_trivial(row) && is_conflict(row) && is_positive_combination(row);
    }

    std::vector<Node> split_into_independent_nodes(const Node& n) const;

    Node unbounded_elimination(Node& parent);
    Node bounded_elimination  (Node& parent);
    bool fm_elimination       (Node& parent);

    Matrix trivial_unsat_matrix() const {
        Matrix result = Matrix(1, m_total_cols);
        std::vector<RowEntry> unsat_row = { RowEntry(constant_column(), Rational(1)) };
        result.append_row(unsat_row.begin(), unsat_row.end());
        return result;
    }
};

}