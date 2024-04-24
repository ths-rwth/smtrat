#pragma once

#include <vector>
#include <set>

#include "Matrix.h"

namespace smtrat::fmplex {

struct Node {
    using RowIndex = Matrix::RowIndex;
    using ColIndex = Matrix::ColIndex;
    
    enum class Type { UNDETERMINED, CONFLICT, LEAF, LBS, UBS, NBS, FM };

    Matrix   matrix;
    Type     type = Type::UNDETERMINED;
    ColIndex chosen_col;
    std::vector<ColIndex> cols_to_elim;
    std::vector<RowIndex> eliminators;
    std::set<RowIndex> ignored;

    Node(bool is_sat) {
        type = is_sat ? (Type::LEAF) : (Type::CONFLICT);
        eliminators.clear();
    }

    Node() {}

    Node(const Matrix& m, const std::vector<ColIndex>& cols)
    : matrix(m)
    , cols_to_elim(cols) {}

    Node(const Matrix& m, const std::vector<ColIndex>& cols, const std::set<RowIndex>& ign)
    : matrix(m)
    , cols_to_elim(cols)
    , ignored(ign) {}

    Node(Matrix&& m, const std::vector<ColIndex>& cols)
    : matrix(std::move(m))
    , cols_to_elim(cols) {}


    inline bool is_conflict() const { return type == Node::Type::CONFLICT; }
    inline bool is_finished() const { return eliminators.empty(); }

    static Node conflict() { return Node(false); }
    static Node leaf()     { return Node(true); }

    void choose_elimination() {
        if (matrix.n_rows() == 0 || cols_to_elim.empty()) {
            type = Node::Type::LEAF;
            return;
        }

        if (cols_to_elim.size() == 1) {
            type = Node::Type::FM;
            chosen_col = cols_to_elim.front();
            return;
        }

        // find best column
        std::size_t min_branches = matrix.n_rows();
        for (const auto j : cols_to_elim) {
            std::size_t lbs = 0, ubs = 0;
            for (const auto& entry : matrix.col_entries(j)) {
                if (entry.value < 0) ++lbs;
                else ++ubs;
            }
            std::size_t min_j = std::min(lbs, ubs);
            if (min_j == 0) {
                chosen_col = j;
                type = Node::Type::NBS;
                break;
            } else if (min_j < min_branches) {
                min_branches = min_j;
                chosen_col = j;
                type = (lbs == min_j) ? Node::Type::LBS : Node::Type::UBS;
            }
        }

        // gather eliminators
        auto col_it  =  matrix.col_begin(chosen_col);
        auto col_end =  matrix.col_end(chosen_col);

        auto ign_it = ignored.begin();
        switch (type) {
        case Node::Type::LBS:
            for (; col_it != col_end; ++col_it) {
                if (ign_it != ignored.end() && *ign_it == col_it.row()) ++ign_it;
                else if (col_it->value < 0) eliminators.push_back(col_it.row());
            }
            break;
        case Node::Type::UBS:
            for (; col_it != col_end; ++col_it){
                if (ign_it != ignored.end() && *ign_it == col_it.row()) ++ign_it;
                else if (col_it->value > 0) eliminators.push_back(col_it.row());
            }
            break;
        case Node::Type::NBS:
            for (; col_it != col_end; ++col_it){
                eliminators.push_back(col_it.row());
            }
            break;
        default:
            break;
        }
    }
};



}