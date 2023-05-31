#pragma once

namespace smtrat::simplex {

using ConflictActivity = double;

struct VariableInfo {
    bool m_is_basic = false;
    bool m_is_integer;
    bool m_is_original;
    ConflictActivity m_conflict_activity = 0;
    std::size_t m_tableau_index = 0; // Row or Column, if basic or non-basic  REVIEW: model as union?
    VariableInfo(bool is_int, bool is_orig) : m_is_integer(is_int), m_is_original(is_orig) {}
};

}