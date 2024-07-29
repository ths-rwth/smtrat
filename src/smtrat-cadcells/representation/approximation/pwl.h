#pragma once

namespace smtrat::cadcells::representation::approximation {

class LinearSegment {
private:
	Rational slope;
	Rational intercept;
	carl::Interval<Rational> domain;

	bool is_poly_ref_set = false;
	cadcells::datastructures::PolyRef poly_ref;

public:
	LinearSegment() = default;
	LinearSegment(Rational slope, Rational intercept, carl::Interval<Rational> domain)
    : slope(slope), intercept(intercept), domain(domain) {
		assert(domain.lower() < domain.upper());
	}
	LinearSegment(Rational a_x, Rational a_y, Rational b_x, Rational b_y) {
		slope = (b_y - a_y) / (b_x - a_x);
		intercept = a_y - (slope * a_x);
		domain = carl::Interval<Rational>(a_x, b_x);
	}

	auto getSlope()     const { return slope; }
	auto getIntercept() const { return intercept; }
	auto getDomain()    const { return domain; }

	Rational evaluate(Rational x) const { return slope * x + intercept; }

	cadcells::datastructures::PolyRef get_poly_ref(cadcells::datastructures::PolyPool &polys, carl::LPPolynomial::ContextType &ctx, carl::Variable var_x, carl::Variable var_y) {
		if(is_poly_ref_set) { return poly_ref; }

		Rational c1 = slope.get_num() * intercept.get_den();
		Rational c2 = slope.get_den() * intercept.get_num();
		Rational c3 = slope.get_den() * intercept.get_den();

		using P = cadcells::Polynomial;

		cadcells::Polynomial res = (P(ctx, var_x) * P(ctx, c1)) + (P(ctx, c2)) - (P(ctx, var_y) * P(ctx, c3));

		poly_ref = polys(res);
		is_poly_ref_set = true;
		return poly_ref;
	}

	// operator<<
	friend std::ostream& operator<<(std::ostream& os, const LinearSegment& segment) {
		os << segment.slope << " * x + " << segment.intercept;
		return os;
	}
};

class PWL {
private:
	std::vector<LinearSegment> segments;

public:
	PWL() = default;
	PWL(const std::vector<LinearSegment>& segments) : segments(segments) {}

	void addSegment(const LinearSegment& segment) { segments.push_back(segment); }

	std::vector<LinearSegment> getSegments() const { return segments; }

	cadcells::datastructures::CompoundMinMax getAsCompoundMinMax(carl::LPPolynomial::ContextType &ctx, cadcells::datastructures::PolyPool& polys, carl::Variable var_x, carl::Variable var_y) const {
		if(segments.size() != 2) {
			throw std::runtime_error("PWL::getAsCompoundMinMax() not implemented for PWLs with more than two segments yet.");
		}

		cadcells::datastructures::CompoundMinMax compoundMinMax;

		auto f1 = segments[0];
		auto f2 = segments[1];

		auto f1_poly = f1.get_poly_ref(polys, ctx, var_x, var_y);
		auto f2_poly = f2.get_poly_ref(polys, ctx, var_x, var_y);

		if(f1.getSlope() < f2.getSlope()) {
			compoundMinMax.roots.emplace_back();
			compoundMinMax.roots.back().emplace_back(f1_poly, 1);
			compoundMinMax.roots.back().emplace_back(f2_poly, 1);
		} else {
			compoundMinMax.roots.emplace_back();
			compoundMinMax.roots.back().emplace_back(f1_poly, 1);
			compoundMinMax.roots.emplace_back();
			compoundMinMax.roots.back().emplace_back(f2_poly, 1);
		}

		return compoundMinMax;
	}

	cadcells::datastructures::CompoundMaxMin getAsCompoundMaxMin(carl::LPPolynomial::ContextType &ctx, cadcells::datastructures::PolyPool& polys, carl::Variable var_x, carl::Variable var_y) const {
		if(segments.size() != 2) {
			throw std::runtime_error("PWL::getAsCompoundMaxMin() not implemented for PWLs with more than two segments yet.");
		}

		cadcells::datastructures::CompoundMaxMin compoundMaxMin;

		auto f1 = segments[0];
		auto f2 = segments[1];

		auto f1_poly = f1.get_poly_ref(polys, ctx, var_x, var_y);
		auto f2_poly = f2.get_poly_ref(polys, ctx, var_x, var_y);

		if(f1.getSlope() >= f2.getSlope()) {
			compoundMaxMin.roots.emplace_back();
			compoundMaxMin.roots.back().emplace_back(f1_poly, 1);
			compoundMaxMin.roots.back().emplace_back(f2_poly, 1);
		} else {
			compoundMaxMin.roots.emplace_back();
			compoundMaxMin.roots.back().emplace_back(f1_poly, 1);
			compoundMaxMin.roots.emplace_back();
			compoundMaxMin.roots.back().emplace_back(f2_poly, 1);
		}

		return compoundMaxMin;
	}
};

}