# pragma once

#include "pwl.h"

namespace smtrat::cadcells::representation::approximation {

class PWLBuilder {
protected:
	std::vector<std::pair<Rational, Rational>> points; // list of points	
	std::vector<Rational> slopes; // list of slopes
	std::vector<Rational> intercepts; // list of y-intercepts
	std::vector<LinearSegment> segments; // map of segments
	std::map<std::pair<std::size_t, std::size_t>, bool> is_over_cache; // map for caching the results of isOver
	std::map<std::pair<std::size_t, std::size_t>, bool> is_under_cache;

	/**
	 * @param i the index of the segment l_i
	 * @param j the index of the segment l_j
	 * @return whether the segment l_i \in I_{\geq,j}
	 */
	inline bool is_over(std::size_t i, std::size_t j) {
		if(i == j) return true;

		// check cache
		auto it = is_over_cache.find(std::make_pair(i, j));
		if(it != is_over_cache.end()) { return it->second; }

		Rational j_m = slopes[j];
		Rational j_left_height = points[j].second;
		Rational j_right_height = points[j+1].second;

		Rational i_m = slopes[i];
		Rational i_left_height = evaluate_segment_at_point(i, points[j].first);
		Rational i_right_height = evaluate_segment_at_point(i, points[j+1].first);

		bool result;
		if(j == 0) result = (i_right_height >= j_right_height && i_m <= j_m);
        else if(j == slopes.size() - 1) result = (i_left_height >= j_left_height && i_m >= j_m);
		else result = (i_left_height >= j_left_height && i_right_height >= j_right_height);

		// insert into cache
		is_over_cache[std::make_pair(i, j)] = result;
		return result;
	}

	/**
     * @param i the index of the segment l_i
     * @param j the index of the segment l_j
     * @return whether the segment l_i \in I_{\leq,j}
	 */
	inline bool is_under(std::size_t i, std::size_t j) {
		if(i == j) return true;

		// check cache
		auto it = is_under_cache.find(std::make_pair(i, j));
		if(it != is_under_cache.end()) { return it->second; }

		Rational j_m = slopes[j];
		Rational j_left_height = points[j].second;
		Rational j_right_height = points[j+1].second;

		Rational i_m = slopes[i];
		Rational i_left_height = evaluate_segment_at_point(i, points[j].first);
		Rational i_right_height = evaluate_segment_at_point(i, points[j+1].first);

		bool result;
		if(j == 0) result = i_right_height <= j_right_height && i_m >= j_m;
        else if(j == slopes.size() - 1) result = i_left_height <= j_left_height && i_m <= j_m;
        else result = i_left_height <= j_left_height && i_right_height <= j_right_height;

		// insert into cache
		is_under_cache[std::make_pair(i, j)] = result;
		return result;
	}

public:
	void debug(const datastructures::IndexedRoot &/*ir*/, const Assignment &/*sample*/, const datastructures::Projections& /*proj*/, const carl::Variable &/*primary_variable*/, const carl::Variable &/*secondary_variable*/) {
		std::cout << "PWLBuilder::debug" << std::endl;
		std::cout << "  points: " << std::endl;
		for (const auto& point : points) std::cout << "    (" << point.first << ", " << point.second << ")" << std::endl;
		std::cout << "  segments: " << std::endl;
		for (const auto& segment : segments) std::cout << "    " << segment << std::endl;
	}

	void add_point(const Rational primary, const Rational secondary) {
		auto insertionPos = std::lower_bound(
			points.begin(), points.end(),
            std::make_pair(primary, Rational(0)),
			[](const auto& lhs, const auto& rhs) { return lhs.first < rhs.first; }
		);

		std::size_t index = static_cast<std::size_t>(std::distance(points.begin(), insertionPos));
		points.insert(insertionPos, std::make_pair(primary, secondary));

		if(points.size() > 1) { recalculate_segments(index); }
	}

	std::pair<Rational, Rational> calculate_segment_properties(std::size_t index1, std::size_t index2) {
		assert(index1 < index2);
		const auto& point1 = points[index1];
		const auto& point2 = points[index2];
		Rational slope = (point2.second - point1.second) / (point2.first - point1.first);
		Rational intercept = point2.second - slope * point2.first;
		return std::make_pair(slope, intercept);
	}

	void recalculate_segments(std::size_t insertionPos) {
		if (insertionPos == 0) {
			carl::Interval<Rational> a_interval(points[insertionPos].first, points[insertionPos + 1].first);
			auto [a_slope, a_intercept] = calculate_segment_properties(insertionPos, insertionPos + 1);
			LinearSegment a_segment(a_slope, a_intercept, a_interval);

			slopes.insert(slopes.begin(), a_slope);
			intercepts.insert(intercepts.begin(), a_intercept);
			segments.insert(segments.begin(), a_segment);
		} else if (insertionPos == points.size() - 1) {
			carl::Interval<Rational> b_interval(points[insertionPos - 1].first, points[insertionPos].first);
			auto [b_slope, b_intercept] = calculate_segment_properties(insertionPos - 1, insertionPos);
			LinearSegment b_segment(b_slope, b_intercept, b_interval);

			slopes.push_back(b_slope);
			intercepts.push_back(b_intercept);
			segments.push_back(b_segment);
		} else {
			carl::Interval<Rational> a_interval(points[insertionPos - 1].first, points[insertionPos].first);
			auto [a_slope, a_intercept] = calculate_segment_properties(insertionPos - 1, insertionPos);
			LinearSegment a_segment(a_slope, a_intercept, a_interval);

			carl::Interval<Rational> b_interval(points[insertionPos].first, points[insertionPos + 1].first);
			auto [b_slope, b_intercept] = calculate_segment_properties(insertionPos, insertionPos + 1);
			LinearSegment b_segment(b_slope, b_intercept, b_interval);

			slopes.insert(slopes.begin() + static_cast<long>(insertionPos), b_slope);
			intercepts.insert(intercepts.begin() + static_cast<long>(insertionPos), b_intercept);
			segments.insert(segments.begin() + static_cast<long>(insertionPos), b_segment);

			slopes[insertionPos - 1] = a_slope;
			intercepts[insertionPos - 1] = a_intercept;
			segments[insertionPos - 1] = a_segment;
		}
	}

	Rational evaluate_segment_at_point(std::size_t segment, Rational point) {
		return slopes[segment] * point + intercepts[segment];
	}

	std::size_t get_number_of_segments() { return segments.size(); }

	LinearSegment get_segment(std::size_t index) {
		assert(index < segments.size());
		return segments[index];
	}

	virtual datastructures::CompoundMinMax build_compound_min_max(carl::LPPolynomial::ContextType& /*ctx*/,
                                                               	  datastructures::PolyPool& /*polys*/,
                                                               	  carl::Variable /*primary_variable*/,
                                                               	  carl::Variable /*secondary_variable*/) = 0;

	virtual datastructures::CompoundMaxMin build_compound_max_min(carl::LPPolynomial::ContextType& /*ctx*/,
                                                               	  datastructures::PolyPool& /*polys*/,
                                                               	  carl::Variable /*primary_variable*/,
                                                               	  carl::Variable /*secondary_variable*/) = 0;
};


class SimplePWLBuilder : public PWLBuilder {
public:
	SimplePWLBuilder() {}

	datastructures::CompoundMinMax build_compound_min_max(carl::LPPolynomial::ContextType &ctx, smtrat::cadcells::datastructures::PolyPool& polys, carl::Variable primary_variable, carl::Variable secondary_variable) {
		datastructures::CompoundMinMax compoundMinMax;

		datastructures::PiecewiseLinearInfo pwlInfo;
		for (std::size_t j = 0; j < slopes.size(); ++j) {
			compoundMinMax.roots.emplace_back();

			LinearSegment definingSegment = get_segment(j);
			auto definingPoly = definingSegment.poly_ref(polys, ctx, primary_variable, secondary_variable);
			auto ir = datastructures::IndexedRoot(definingPoly, 1);

			for(std::size_t i = 0; i < slopes.size(); ++i) {
				if(is_under(i, j)) {
					LinearSegment segment = get_segment(i);
					auto polynomial = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);
					compoundMinMax.roots.back().emplace_back(polynomial, 1);
				}
			}

			if(j == 0) {
				pwlInfo.first = ir;
			} else {
				pwlInfo.bounds.push_back( {points[j].first, ir} );
			}
		}

		compoundMinMax.bounds = pwlInfo;

		return compoundMinMax;
	}

	datastructures::CompoundMaxMin build_compound_max_min(carl::LPPolynomial::ContextType &ctx, smtrat::cadcells::datastructures::PolyPool& polys, carl::Variable primary_variable, carl::Variable secondary_variable) {
		datastructures::CompoundMaxMin compoundMaxMin;

		datastructures::PiecewiseLinearInfo pwlInfo;
		for(std::size_t j = 0; j < slopes.size(); ++j) {
			compoundMaxMin.roots.emplace_back();

			LinearSegment definingSegment = get_segment(j);
			auto definingPoly = definingSegment.poly_ref(polys, ctx, primary_variable, secondary_variable);
			auto ir = datastructures::IndexedRoot(definingPoly, 1);

			for(std::size_t i = 0; i < slopes.size(); ++i) {
				if(is_over(i, j)) {
					LinearSegment segment = get_segment(i);
					auto polynomial = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);
					compoundMaxMin.roots.back().emplace_back(polynomial, 1);
				}
			}

			if(j == 0) {
				pwlInfo.first = ir;
			} else {
				pwlInfo.bounds.push_back( {points[j].first, ir} );
			}
		}

		compoundMaxMin.bounds = pwlInfo;

		return compoundMaxMin;
	}

};



class AdvancedPWLBuilder : public PWLBuilder {
public:
	AdvancedPWLBuilder() {}

	datastructures::CompoundMinMax build_compound_min_max(carl::LPPolynomial::ContextType& ctx, smtrat::cadcells::datastructures::PolyPool& polys, carl::Variable primary_variable, carl::Variable secondary_variable) {
		datastructures::CompoundMinMax compoundMinMax;
		datastructures::PiecewiseLinearInfo pwlInfo;

		for (std::size_t i = 0; i < slopes.size(); ++i) {
			compoundMinMax.roots.emplace_back();

			LinearSegment definingSegment = get_segment(i);
			auto definingPoly = definingSegment.poly_ref(polys, ctx, primary_variable, secondary_variable);
			auto definingIR = datastructures::IndexedRoot(definingPoly, 1);

			compoundMinMax.roots.back().emplace_back(definingPoly, 1);

			for (std::size_t j = 0; j < slopes.size(); ++j) {
				if (i == j) continue;
				if (is_over(i, j)) continue;

				if (is_under(j, i)) {
					LinearSegment segment = get_segment(j);
					auto poly = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);

					compoundMinMax.roots.back().emplace_back(poly, 1);
					continue;
				}

				bool found = false;

				std::size_t smaller = (i < j) ? i : j;
				std::size_t bigger = (i > j) ? i : j;
				for (std::size_t k = smaller + 1; k < bigger; ++k) {
					if (is_under(k, i) && is_over(k, j)) {
						LinearSegment segment = get_segment(k);
						auto poly = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);

						compoundMinMax.roots.back().emplace_back(poly, 1);

						found = true;
						break;
					}
				}

				assert(found);
			}

			if (i == 0) pwlInfo.first = definingIR;
            else pwlInfo.bounds.push_back({points[i].first, definingIR});
		}

		compoundMinMax.bounds = pwlInfo;
		return compoundMinMax;
	}

	datastructures::CompoundMaxMin build_compound_max_min(carl::LPPolynomial::ContextType& ctx, smtrat::cadcells::datastructures::PolyPool& polys, carl::Variable primary_variable, carl::Variable secondary_variable) {
		datastructures::CompoundMaxMin compoundMaxMin;
		datastructures::PiecewiseLinearInfo pwlInfo;

		for (std::size_t i = 0; i < slopes.size(); ++i) {
			compoundMaxMin.roots.emplace_back();

			LinearSegment definingSegment = get_segment(i);
			auto definingPoly = definingSegment.poly_ref(polys, ctx, primary_variable, secondary_variable);
			auto definingIR = datastructures::IndexedRoot(definingPoly, 1);

			compoundMaxMin.roots.back().emplace_back(definingPoly, 1);

			for (std::size_t j = 0; j < slopes.size(); ++j) {
				if (i == j) continue;
				if (is_under(i, j)) continue;

				if (is_over(j, i)) {
					LinearSegment segment = get_segment(j);
					auto poly = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);

					compoundMaxMin.roots.back().emplace_back(poly, 1);
					continue;
				}

				bool found = false;

				std::size_t smaller = i < j ? i : j;
				std::size_t bigger = i > j ? i : j;
				for (std::size_t k = smaller + 1; k < bigger; ++k) {
					if (is_over(k, i) && is_under(k, j)) {
						LinearSegment segment = get_segment(k);
						auto poly = segment.poly_ref(polys, ctx, primary_variable, secondary_variable);

						compoundMaxMin.roots.back().emplace_back(poly, 1);

						found = true;
						break;
					}
				}
				assert(found);
			}

			if (i == 0) pwlInfo.first = definingIR;
            else pwlInfo.bounds.push_back({points[i].first, definingIR});
		}

		compoundMaxMin.bounds = pwlInfo;
		return compoundMaxMin;
	}
};



}