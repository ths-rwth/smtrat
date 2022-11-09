#pragma once

#include "Tableau.h"
#include <smtrat-common/smtrat-common.h>
namespace smtrat{
    class Level {
        public:
            Level(const FormulasT& constraints) : m_tableau(constraints) {
                
            }

        private:
            /// The tableau representing the constraint set at that level
            Tableau<Rational> m_tableau;
            /// Indicates which of the tableau's rows have been tried as eliminators
            std::vector<std::size_t> m_tried_rows;
            /// Indicates which of the tableau's rows can still be tried as eliminators
            std::vector<std::size_t> m_open_rows;
            /// The column index corresponding to the eliminated variable
            std::size_t m_elimination_variable_idx;
            /// The row index corresponding to the currently used eliminator
            std::size_t m_current_eliminator_idx; // TODO what happens for special elimination with only one bound type?

            std::vector<std::size_t> m_backtrack_levels;
            std::vector<carl::Relation> m_relations;

        public:
            carl::Variable choose_variable()

            bool checked_all_eliminators() {
                return m_open_rows.empty();
            }

            Level next_child() {
                // TODO
            }

            Rational find_variable_assignment(const Model& m) {
                // TODO
            }
    };
}