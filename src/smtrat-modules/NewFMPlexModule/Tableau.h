#include <eigen3/Eigen/Sparse>

namespace smtrat{
    template<typename Number>
    class Tableau {
        private:
            using Matrix = Eigen::SparseMatrix<Number, Eigen::RowMajor>;
            using MatrixEntry = Eigen::Triplet<Number>;
            using MatrixEntries = std::vector<MatrixEntry>;

            Matrix m_matrix;
            carl::Bitset m_strict_rows;

            
        public:
            Tableau(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) {
                MatrixEntries entries();
                entries.reserve(constraints.size() * variable_index.size());
                for (std::size_t row = 0; row < constraints.size(); row++) {
                    const FormulaT& c = constraints[i];
                    carl::Relation r = c.constraint().relation();
                    Poly p = c.constraint().lhs();
                    if (r == carl::Relation::GEQ || r == carl::Relation::GREATER) {
                        for (const auto& term : p) {
                            std::size_t column = term.is_constant() ? variable_index.size() : variable_index[term.single_variable()];
                            entries.emplace_back(row, column, -term.coeff());
                        }
                    } else { // r == LEQ or r == LESS
                        for (const auto& term : p) {
                            std::size_t column = term.is_constant() ? variable_index.size() : variable_index[term.single_variable()];
                            entries.emplace_back(row, column, term.coeff());
                        }
                    }
                }
                m_matrix(constraints.size(), variable_index.size()+1);
                m_matrix.setFromTriplets(entries);
            }
    };
}