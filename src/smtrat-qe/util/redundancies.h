#pragma once
#include "Matrix.h"
#include <smtrat-solver/Manager.h>
#include <smtrat-modules/SimplexModule/SimplexModule.h>

namespace smtrat::qe::util {

enum class Redundancy {
    FIRST_IMPLIES_SECOND, SECOND_IMPLIES_FIRST, NONE
};


template<typename Row>
inline Redundancy compare_rows(const Row& row1, const Row& row2, const std::size_t constant_index) {
    auto it1 = row1.begin();
    auto it2 = row2.begin();
    if (it1->col_index != it2->col_index) return Redundancy::NONE;
    Rational scale = it1->value / it2->value;
    if (scale < 0) return Redundancy::NONE;
    while (it1 != row1.end() && it2 != row2.end()) {
        if ((it1->col_index >= constant_index) && (it2->col_index >= constant_index)) {
            if (it1->col_index > it2->col_index) {
                if (it2->col_index > constant_index + 1) return Redundancy::FIRST_IMPLIES_SECOND;
                return (it2->value > 0) ? Redundancy::SECOND_IMPLIES_FIRST
                                        : Redundancy::FIRST_IMPLIES_SECOND;
            }
            if (it1->col_index < it2->col_index) {
                if (it1->col_index > constant_index + 1) return Redundancy::FIRST_IMPLIES_SECOND;
                return (it1->value > 0) ? Redundancy::FIRST_IMPLIES_SECOND
                                        : Redundancy::SECOND_IMPLIES_FIRST;
            }
            assert(it1->col_index == it2->col_index);
            return ((scale * it2->value) > it1->value) ? Redundancy::SECOND_IMPLIES_FIRST
                                                       : Redundancy::FIRST_IMPLIES_SECOND;
        }
        if ((it1->col_index != it2->col_index) || (scale != it1->value / it2->value)) {
            return Redundancy::NONE;
        }
        ++it1;
        ++it2;
    }
    return Redundancy::NONE;
}


inline std::vector<Matrix::RowIndex> simple_irredundant_rows(const Matrix& m,
                                                             const std::size_t constant_index) {
    std::set<std::size_t> skips;
    std::vector<Matrix::RowIndex> result;
    for (Matrix::RowIndex r = 0; r < m.n_rows(); ++r) {
        if (std::find(skips.begin(), skips.end(), r) != skips.end()) continue;
        bool is_irredundant = true;
        for (Matrix::RowIndex s = r+1; s < m.n_rows(); ++s) {
            if (std::find(skips.begin(), skips.end(), s) != skips.end()) continue;
            auto red = compare_rows(m.row_entries(r), m.row_entries(s), constant_index);
            if (red == Redundancy::FIRST_IMPLIES_SECOND) skips.insert(s);
            else if (red == Redundancy::SECOND_IMPLIES_FIRST) {
                is_irredundant = false;
                break;
            }
        }
        if (is_irredundant) { result.push_back(r); }
    }
    return result;
}


class Simplex : public smtrat::Manager {
    public:
        Simplex(): Manager() {
            setStrategy({ addBackend<SimplexModule<SimplexSettings1>>() });
        }
    };

inline std::vector<std::size_t> irredundant_rows(const FormulasT& constraints, const FormulasT& core) {
    auto solver = Simplex();
    for (const auto& f : core) solver.inform(f);
    for (const auto& f : constraints) solver.inform(f);
    for (const auto& f : constraints) solver.inform(f.negated());
    for (const auto& f : core) solver.add(f);
    for (const auto& f : constraints) solver.add(f);

    std::vector<std::size_t> result;
    for (std::size_t i = 0; i < constraints.size(); ++i) {
        solver.remove(constraints[i]);
        solver.add(constraints[i].negated());

        if(solver.check() == Answer::UNSAT) {
            solver.remove(constraints[i].negated());
        } else {            
            // irredundant
            solver.remove(constraints[i].negated());
            solver.add(constraints[i]);
            result.push_back(i);
        }
    }
    return result;
}


}