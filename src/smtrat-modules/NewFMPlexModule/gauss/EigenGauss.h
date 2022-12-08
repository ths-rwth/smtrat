#include <eigen3/Eigen/Sparse>
#include <eigen3/Eigen/SparseQR>

namespace smtrat::fmplex{

class EigenGauss : Gauss {
    private:

	using Matrix = Eigen::SparseMatrix<Rational, Eigen::ColMajor>;
	using Vector = Eigen::SparseVector<Rational>;

	Matrix m_matrix;
	Vector m_rhs;
	FormulasT m_inequalities;

    public:
    void init(const FormulasT& constraints, const std::map<carl::Variable, std::size_t>& variable_index) override {
		std::vector<Eigen::Triplet<Rational>> matrix_entries;
		std::vector<std::pair<std::size_t, Rational>> vector_entries;
		std::size_t n_equalities = 0;

		for (std::size_t row = 0; row < constraints.size(); row++) {
			n_equalities++;
			auto constraint = constraints[row].constraint();
			if (constraint.relation() == carl::Relation::EQ) {
				Poly p = constraint.lhs();
				for (const auto& term : p) {
					if (term.is_constant()) vector_entries.emplace_back(n_equalities, -term.coeff());
					else matrix_entries.emplace_back(row, variable_index.at(term.single_variable()), term.coeff());
				}
			} else {
				m_inequalities.push_back(constraints[row]);
			}
		}

		m_matrix = Matrix(n_equalities, variable_index.size());
		m_matrix.setFromTriplets(matrix_entries.begin(), matrix_entries.end());

		m_rhs = Vector(n_equalities);
		for (const auto [i, v_i] : vector_entries) m_rhs.insertBack(i) = v_i;
    }

    void apply_gaussian_elimination() override {
		m_matrix.makeCompressed();
		Eigen::SparseQR<Matrix, Eigen::COLAMDOrdering<int>> solver; // REVIEW: different ordering?
		solver.compute(m_matrix);
		if(solver.info() != Eigen::Success) {
			assert(false); // TODO: not yet implemented or // unreachable
		}
		// TODO: compute transformed rhs
		// TODO: compute transformed inequalities
		// TODO: compute origins
    }

    FMPlexTableau get_transformed_inequalities() override {
        // TODO: not yet implemented
    }
};

} // namespace smtrat::fmplex