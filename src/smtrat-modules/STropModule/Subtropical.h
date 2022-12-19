#pragma once

#include <carl-arith/constraint/BasicConstraint.h>
#include <boost/container/flat_map.hpp>

/**
 * Implements data structures and encodings for the subtropical method.
 *
 *
 */
namespace smtrat::subtropical {

enum class SeparatorType { STRICT = 0,
						   WEAK = 1,
						   SEMIWEAK = 2 };

/**
 * Represents the normal vector component and the sign variable
 * assigned to a variable in an original constraint.
 */
struct Moment {
	/// Normal vector component of the separating hyperplane
	const carl::Variable normal_vector;
	/// Boolean variable representing the sign variant
	const carl::Variable sign_variant;

	Moment()
		: normal_vector(carl::fresh_real_variable()), sign_variant(carl::fresh_boolean_variable()) {}
};

/**
 * Represents a term of an original constraint and assigns
 * him a rating variable if a weak separator is searched.
 */
struct Vertex {
	/// Coefficient of the assigned term
	const Rational coefficient;
	/// Monomial of the assigned term
	const carl::Monomial::Arg monomial;
	/// Rating variable of the term for a weak separator
	mutable carl::Variable m_rating;

	Vertex(const TermT& term)
		: coefficient(term.coeff()), monomial(term.monomial()), m_rating(carl::Variable::NO_VARIABLE) {}

	carl::Variable rating() const {
		if (m_rating == carl::Variable::NO_VARIABLE) m_rating = carl::fresh_real_variable();
		return m_rating;
	}
};

/// Subdivides the relations into classes with the same linearization result
enum class Direction { BOTH = 0,
					   NEGATIVE = 1,
					   POSITIVE = 2 };

inline carl::BasicConstraint<Poly> normalize(const carl::BasicConstraint<Poly>& c) {
	assert(c.relation() == carl::Relation::LESS || c.relation() == carl::Relation::LEQ || c.relation() == carl::Relation::EQ || c.relation() == carl::Relation::NEQ);
	return carl::BasicConstraint<Poly>(c.lhs().normalize(), carl::is_negative(c.lhs().lcoeff()) ? carl::turn_around(c.relation()) : c.relation());
}

inline std::optional<Direction> direction(carl::Relation r) {
	switch (r) {
	case carl::Relation::GREATER:
	case carl::Relation::GEQ:
		return Direction::POSITIVE;
		break;
	case carl::Relation::LESS:
	case carl::Relation::LEQ:
		return Direction::NEGATIVE;
		break;
	case carl::Relation::NEQ:
		return Direction::BOTH;
		break;
	default:
		return std::nullopt;
	}
}

/**
 * Represents the class of all original constraints with the same
 * left hand side after a normalization. Here, the set of all received
 * relations of constraints with the same left hand side is stored. At any
 * one time only one relation can be active and used for linearization.
 */
struct Separator {
	/// Bias variable of the separating hyperplane
	const carl::Variable bias;
	/// Vertices for all terms of the normalized left hand side
	const std::vector<Vertex> vertices;

	Separator(const Poly& normalization)
		: bias(carl::fresh_real_variable()), vertices(normalization.begin(), normalization.end()) {}
};

inline std::optional<Direction> direction_for_equality(const Separator& s) {
    // compute point (1,...,1) at polynomial
    Rational sum_of_coeffs = 0;
    for(const auto& v : s.vertices){
        sum_of_coeffs += v.coefficient;
    }
    if (sum_of_coeffs == 0) return std::nullopt; // root found
    else return (sum_of_coeffs < 0) ? subtropical::Direction::POSITIVE : subtropical::Direction::NEGATIVE;
}

class Encoding {
	/// Maps a variable to the components of the moment function
	std::unordered_map<carl::Variable, Moment> m_moments;

public:
	/**
	 * Creates the formula for the hyperplane that linearly separates at least one
	 * variant positive frame vertex from all variant negative frame vertices. If a
	 * weak separator is searched, the corresponding rating is included.
	 * @param separator The separator object that stores the construction information.
	 * @param negated True, if the formula for the negated polynomial shall be constructed.
	 * 				  False, if the formula for the original polynomial shall be constructed.
	 * @return Formula that is satisfiable iff such a separating hyperplane exists.
	 */
	inline FormulaT encode_separator(const Separator& separator, const Direction direction, const SeparatorType separator_type) {
		if (direction == Direction::BOTH) {
			return FormulaT(carl::FormulaType::XOR,
							encode_separator(separator, Direction::POSITIVE, separator_type),
							encode_separator(separator, Direction::NEGATIVE, separator_type));
		} else {
			assert(direction == Direction::NEGATIVE || direction == Direction::POSITIVE);
			bool negated = (direction == Direction::NEGATIVE);
			Poly totalRating;
			FormulasT disjunctions, conjunctions;
			for (const Vertex& vertex : separator.vertices) {
				/// Create the hyperplane and sign change formula
				Poly hyperplane{separator.bias};
				FormulaT signChangeFormula;
				if (vertex.monomial) {
					FormulasT signChangeSubformulas;
					for (const auto& exponent : vertex.monomial->exponents()) {
						const auto& moment{m_moments[exponent.first]};
						hyperplane += carl::from_int<Rational>(exponent.second) * moment.normal_vector;
						if (exponent.second % 2 == 1)
							signChangeSubformulas.emplace_back(moment.sign_variant);
					}
					signChangeFormula = FormulaT(carl::FormulaType::XOR, std::move(signChangeSubformulas));
				}

				/// Create the rating case distinction formula
				if (separator_type == SeparatorType::WEAK) {
					totalRating += vertex.rating();
					conjunctions.emplace_back(
						carl::FormulaType::IMPLIES,
						FormulaT(hyperplane, carl::Relation::LESS),
						FormulaT(Poly(vertex.rating()), carl::Relation::EQ));
					const Rational coefficient{negated ? -vertex.coefficient : vertex.coefficient};
					conjunctions.emplace_back(
						carl::FormulaType::IMPLIES,
						FormulaT(hyperplane, carl::Relation::EQ),
						FormulaT(
							carl::FormulaType::AND,
							FormulaT(
								carl::FormulaType::IMPLIES,
								signChangeFormula,
								FormulaT(vertex.rating() + coefficient, carl::Relation::EQ)),
							FormulaT(
								carl::FormulaType::IMPLIES,
								signChangeFormula.negated(),
								FormulaT(vertex.rating() - coefficient, carl::Relation::EQ))));
				}

				/// Create the strict/weak linear separating hyperplane
				bool positive{carl::is_positive(vertex.coefficient) != negated};
				disjunctions.emplace_back(
					FormulaT(
						carl::FormulaType::IMPLIES,
						positive ? signChangeFormula.negated() : signChangeFormula,
						FormulaT(hyperplane, separator_type == SeparatorType::STRICT || separator_type == SeparatorType::SEMIWEAK ? carl::Relation::LEQ : carl::Relation::LESS))
						.negated());
				conjunctions.emplace_back(
					carl::FormulaType::IMPLIES,
					positive ? std::move(signChangeFormula) : std::move(signChangeFormula.negated()),
					FormulaT(std::move(hyperplane), separator_type == SeparatorType::STRICT ? carl::Relation::LESS : carl::Relation::LEQ));
			}
			if (separator_type == SeparatorType::WEAK)
				conjunctions.emplace_back(totalRating, carl::Relation::GREATER);
			return FormulaT(
				carl::FormulaType::AND,
				FormulaT(carl::FormulaType::OR, std::move(disjunctions)),
				FormulaT(carl::FormulaType::AND, std::move(conjunctions)));
		}
	}

	inline FormulaT encode_integer(carl::Variable var) {
		auto& moment = m_moments.at(var);
		return FormulaT(Poly(moment.normal_vector), carl::Relation::GEQ);
	}

	inline Model construct_assignment(const Model& lra_model, const FormulaT& f) const {
		/// Stores all informations retrieved from the LRA solver to construct the model
		struct Weight {
			const carl::Variable& variable;
			Rational exponent;
			const bool sign;
			Weight(const carl::Variable& var, const Rational& exp, const bool sgn)
				: variable(var), exponent(exp), sign(sgn) {}
		};
		std::vector<Weight> weights;

		auto used_vars = carl::variables(f);

		// Retrieve the sign and exponent for every active variable
		Rational gcd(0);
		for (const auto& momentsEntry : m_moments) {
			const carl::Variable& variable{momentsEntry.first};
			const Moment& moment{momentsEntry.second};
			if (used_vars.has(variable)) {
				auto signIter{lra_model.find(moment.sign_variant)};
				weights.emplace_back(variable, lra_model.at(moment.normal_vector).asRational(), signIter != lra_model.end() && signIter->second.asBool());
				carl::gcd_assign(gcd, weights.back().exponent);
			}
		}

		// get assignment for (Boolean) variables from original formula
		Model lra_model_nonenc;
		for (const auto& v : used_vars) {
			if (lra_model.find(v) != lra_model.end()) {
				lra_model_nonenc.emplace(v, lra_model.at(v));
			}
		}

		// Calculate smallest possible integer valued exponents
		if (!carl::is_zero(gcd) && !carl::is_one(gcd))
			for (Weight& weight : weights)
				weight.exponent /= gcd;

		// Find model by increasingly testing the sample base
		Model result;
		Rational base = 0;
		do {
			result = lra_model_nonenc;
			++base;
			for (const Weight& weight : weights) {
				Rational value{carl::is_negative(weight.exponent) ? carl::reciprocal(base) : base};
				carl::pow_assign(value, carl::to_int<carl::uint>(carl::abs(weight.exponent)));
				if (weight.sign)
					value *= -1;
				result.emplace(weight.variable, value);
			}
		} while (!satisfied_by(f, result));
		return result;
	}
};

/**
 * Requires a quantifier-free real arithmetic formula with no negations
 *
 * @param formula The formula to transform
 *
 * @return an equisatisfiable equation
 */
inline FormulaT transform_to_equation(const FormulaT& formula) {
	if (formula.type() == carl::FormulaType::TRUE || formula.type() == carl::FormulaType::FALSE) {
		return formula;
	} else if (formula.type() == carl::FormulaType::CONSTRAINT) {
		carl::Relation relation = formula.constraint().relation();
		Poly polynomial = formula.constraint().lhs();
		if (relation == carl::Relation::EQ) {
			return formula;
		}
		Poly transformedPolynomial{polynomial};
		Poly parameter{carl::fresh_real_variable()};
		switch (relation) {
		case carl::Relation::GREATER:
			transformedPolynomial *= (parameter *= parameter);
			transformedPolynomial -= Poly{Rational(1)};
			break;
		case carl::Relation::GEQ:
			transformedPolynomial -= (parameter *= parameter);
			break;
		case carl::Relation::LESS:
			transformedPolynomial *= (parameter *= parameter);
			transformedPolynomial += Poly{Rational(1)};
			break;
		case carl::Relation::LEQ:
			transformedPolynomial += (parameter *= parameter);
			break;
		case carl::Relation::NEQ:
			transformedPolynomial *= parameter;
			transformedPolynomial += Poly{Rational(1)};
			break;
		default:
			assert(false);
			return FormulaT();
		}
		return FormulaT(transformedPolynomial, carl::Relation::EQ);
	} else if (formula.type() == carl::FormulaType::OR) {
		Poly product{Rational(1)};
		for (const auto& subformula : formula.subformulas()) {
			FormulaT transformed = transform_to_equation(subformula);
			if (transformed.type() == carl::FormulaType::TRUE) {
				return transformed;
			} else if (transformed.type() != carl::FormulaType::FALSE) {
				product *= transformed.constraint().lhs();
			}
		}
		return FormulaT(product, carl::Relation::EQ);
	} else if (formula.type() == carl::FormulaType::AND) {
		return FormulaT(carl::FormulaType::FALSE);
	} else {
		assert(false);
		return FormulaT(carl::FormulaType::FALSE);
	}
}

/**
 * Requires a quantifier-free real arithmetic formula with no negations
 *
 * @param formula The formula to translate
 *
 * @return linear formula
 */
inline FormulaT encode_as_formula(const FormulaT& formula, Encoding& encoding, SeparatorType separator_type) {
	if (formula.type() == carl::FormulaType::TRUE || formula.type() == carl::FormulaType::FALSE) {
		return formula;
	} else if (formula.type() == carl::FormulaType::BOOL) {
		return formula;
	} else if (formula.type() == carl::FormulaType::NOT) {
		assert(formula.subformula().type() == carl::FormulaType::BOOL);
		return formula;
	} else if (formula.type() == carl::FormulaType::CONSTRAINT) {
		if (formula.constraint().relation() == carl::Relation::EQ) {
			return FormulaT(carl::FormulaType::FALSE);
		}
		auto constr = normalize(formula.constraint().constr());
		Separator separator(constr.lhs());
		Direction dir = *direction(constr.relation());
		return encoding.encode_separator(separator, dir, separator_type);
	} else if (formula.type() == carl::FormulaType::OR) {
		FormulasT disjunctions;
		for (const auto& subformula : formula.subformulas()) {
			disjunctions.push_back(encode_as_formula(subformula, encoding, separator_type));
		}
		return FormulaT(carl::FormulaType::OR, std::move(disjunctions));
	} else if (formula.type() == carl::FormulaType::AND) {
		FormulasT conjunctions;
		for (const auto& subformula : formula.subformulas()) {
			conjunctions.push_back(encode_as_formula(subformula, encoding, separator_type));
		}
		return FormulaT(carl::FormulaType::AND, std::move(conjunctions));
	} else {
		assert(false);
		return FormulaT(carl::FormulaType::FALSE);
	}
}

/**
 * Requires a quantifier-free real arithmetic formula with no negations
 *
 * @param formula The formula to translate
 *
 * @return linear formula
 */
inline FormulaT encode_as_formula_alt(const FormulaT& formula, Encoding& encoding, SeparatorType separator_type) {
	std::vector<FormulaT> constraints;
	carl::arithmetic_constraints(formula, constraints);
	std::set<FormulaT> constraint_set(constraints.begin(), constraints.end());
	auto res_boolean = formula;
	std::map<Poly, boost::container::flat_map<carl::Relation, std::pair<FormulaT, FormulaT>>> encodings;
	for (const auto& c : constraint_set) {
		if (c.constraint().relation() == carl::Relation::EQ) {
			res_boolean = carl::substitute(res_boolean, c, FormulaT(carl::FormulaType::FALSE));
		} else {
			auto constr = normalize(c.constraint().constr());
			Separator separator(constr.lhs());
			Direction dir = *direction(constr.relation());
			auto& map = encodings.try_emplace(constr.lhs()).first->second;
			assert(map.find(constr.relation()) == map.end());
			FormulaT var = map.find(carl::inverse(constr.relation())) == map.end() ? FormulaT(carl::fresh_boolean_variable()) : map.at(carl::inverse(constr.relation())).first.negated();
			map.emplace(constr.relation(), std::make_pair(var, encoding.encode_separator(separator, dir, separator_type)));
			res_boolean = carl::substitute(res_boolean, c, var);
		}
	}
	std::vector<FormulaT> res({res_boolean});
	for (auto& poly : encodings) {
		for (auto rel = poly.second.begin(); rel != poly.second.end(); ) {
			auto& enc = rel->second;
			bool relevant = false;
			carl::visit(res_boolean, [&enc, &relevant](const FormulaT& f) { if (f==enc.first) relevant = true; } );
			if (relevant) {
				res.emplace_back(carl::FormulaType::IMPLIES, enc.first, enc.second);
				//res.emplace_back(carl::FormulaType::IFF, enc.first, enc.second);
				rel++;
			} else {
				rel = poly.second.erase(rel);
			}
		}
		if (poly.second.find(carl::Relation::LESS) != poly.second.end() && poly.second.find(carl::Relation::GREATER) != poly.second.end()) {
			res.emplace_back(carl::FormulaType::OR, poly.second.at(carl::Relation::LESS).first.negated(), poly.second.at(carl::Relation::GREATER).first.negated());
		}
		if (poly.second.find(carl::Relation::LEQ) != poly.second.end() && poly.second.find(carl::Relation::GEQ) != poly.second.end()) {
		 	res.emplace_back(carl::FormulaType::OR, poly.second.at(carl::Relation::LEQ).first.negated(), poly.second.at(carl::Relation::GEQ).first.negated());
		}
	}
	return FormulaT(carl::FormulaType::AND, std::move(res));
}

} // namespace smtrat::subtropical