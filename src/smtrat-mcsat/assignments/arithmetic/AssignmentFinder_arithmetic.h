#pragma once

#include "Covering.h"
#include "RootIndexer.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>

#include <boost/variant.hpp>

#include <algorithm>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

using carl::operator<<;

class AssignmentFinder_detail {
public:
	using RAN = carl::RealAlgebraicNumber<Rational>;
private:
	carl::Variable mVar;
	const Model& mModel;
	RootIndexer mRI;
	/**
	 * Maps the input formula to the list of real roots and the simplified formula where mModel was substituted.
	 */
	std::map<FormulaT, std::pair<std::vector<RAN>, FormulaT>> mRootMap;
	std::vector<FormulaT> mMVBounds;
	
	/// Checks whether a formula is univariate, meaning it contains mVar and only variables from mModel otherwise.
	bool isUnivariate(const FormulaT& f) const {
		return mcsat::constraint_type::isUnivariate(f, mModel, mVar);
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "is " << f << " univariate in " << mVar << "?");
		carl::Variables vars;
		f.arithmeticVars(vars);
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Collected " << vars);
		auto it = vars.find(mVar);
		if (it == vars.end()) return false;
		vars.erase(it);
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Checking whether " << mModel << " covers " << vars);
		return mModel.contains(vars);
	}
	bool satisfies(const FormulaT& f, const RAN& r) const {
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", f << ", " << mModel << ", " << mVar << ", " << r);
		Model m = mModel;
		m.assign(mVar, r);
		auto res = carl::model::evaluate(f, m);
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Evaluating " << f << " on " << m << " -> " << res);
		if (!res.isBool()) return true;
		assert(res.isBool());
		return res.asBool();
	}
	
	bool compare_assignments(std::size_t lhs, std::size_t rhs) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", lhs << " < " << rhs << "?");
		const auto& l = mRI.sampleFrom(lhs);
		const auto& r = mRI.sampleFrom(rhs);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", l << " (" << mRI.is_root(lhs) << ") < " << r << " (" << mRI.is_root(rhs) << ") ?");
		if ((l.is_integral() || l.is_numeric()) && (r.is_integral() || r.is_numeric()) && (mRI.is_root(lhs) != mRI.is_root(rhs))) return mRI.is_root(lhs);
		if (l.is_integral() != r.is_integral()) return l.is_integral();
		if (l.is_numeric() != r.is_numeric()) return l.is_numeric();
		if (l.size() != r.size()) return l.size() < r.size();
		if (l.abs() != r.abs()) return l.abs() < r.abs();
		return l < r;
	}
	
	ModelValue selectAssignment(const Covering& cover) const {
		std::vector<std::size_t> samples;
		for (auto b: cover.satisfyingSamples()) {
			samples.push_back(b);
		}
		assert(samples.size() > 0);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Finding minimum from " << samples);
		auto min = std::min_element(samples.begin(), samples.end(), [this](auto lhs, auto rhs){ return this->compare_assignments(lhs, rhs); });
		return mRI.sampleFrom(*min);	
	}
	
public:
	AssignmentFinder_detail(carl::Variable var, const Model& model): mVar(var), mModel(model) {}
	
	bool addConstraint(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);
		auto category = mcsat::constraint_type::categorize(f, mModel, mVar);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " is " << category << " under " << mModel << " w.r.t. " << mVar);
		switch (category) {
			case mcsat::ConstraintType::Constant:
				assert(f.isTrue() || f.isFalse());
				if (f.isFalse()) return false;
				break;
			case mcsat::ConstraintType::Assigned: {
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Checking fully assigned " << f);
				FormulaT fnew = carl::model::substitute(f, mModel);
				if (fnew.isTrue()) {
					SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Ignoring " << f << " which simplified to true.");
					return true;
				} else {
					assert(fnew.isFalse());
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
					return false;
				}
				break;
			}
			case mcsat::ConstraintType::Univariate:
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Considering univariate constraint " << f);
				break;
			case mcsat::ConstraintType::Unassigned:
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Considering unassigned constraint " << f << " (which may still become univariate)");
				return true;
				break;
		}
		FormulaT fnew(carl::model::substitute(f, mModel));
		std::vector<RAN> list;
		if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
			const auto& poly = fnew.constraint().lhs();
			SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Real roots of " << poly << " in " << mVar << " w.r.t. " << mModel);
			auto roots = carl::model::tryRealRoots(poly, mVar, mModel);
			if (roots) {
				list = *roots;
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "-> " << list);
			} else {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Failed to compute roots because polynomial is not univariate or became zero.");
				mMVBounds.emplace_back(f);
				return true;
			}
		} else if (fnew.isTrue()) {
			SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Ignoring " << f << " which simplified to true.");
			return true;
		} else {
			assert(fnew.isFalse());
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
			return false;
		}
		
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << list << " with " << fnew);
		mRI.add(list);
		mRootMap.emplace(f, std::make_pair(std::move(list), fnew));
		return true;
	}
	
	bool addMVBound(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::VARCOMPARE);
		if (!isUnivariate(f)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Ignoring non-univariate bound " << f);
			return true;
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding univariate bound " << f);
		FormulaT fnew(carl::model::substitute(f, mModel));
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "-> " << fnew);
		if (fnew.isTrue()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Bound evaluated to true, we can ignore it.");
			return true;
		} else if (fnew.isFalse()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
			return false;
		}
		assert(fnew.getType() == carl::FormulaType::VARCOMPARE);
		ModelValue value = fnew.variableComparison().value();
		if (value.isSubstitution()) {
			// Prevent memory error due to deallocation of shared_ptr before copying value from shared_ptr.
			auto res = value.asSubstitution()->evaluate(mModel);
			value = res;
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Evaluated to " << value);
		if (!value.isRational() && !value.isRAN()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Value is neither rational nor RAN, cannot generate roots from it");
			if (value.isBool()) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "But it is bool");
				assert(false);
			}
			mMVBounds.emplace_back(fnew);
			return true;
		}
		std::vector<RAN> list;
		if (value.isRational()) list.emplace_back(value.asRational());
		else list.push_back(value.asRAN());
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << list << " with " << fnew);
		mRI.add(list);
		mRootMap.emplace(f, std::make_pair(std::move(list), fnew));
		return true;
	}
	
	Covering computeCover() {
		mRI.process();
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", mRI);
		Covering cover(mRI.size() * 2 + 1);
		for (const auto& c: mRootMap) {
			carl::Bitset b;
			const auto& roots = c.second.first; // sorted
			const auto& constraint = c.second.second;
			std::size_t last = 0;
			for (const auto& r: roots) {
				std::size_t cur = mRI[r];
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(2*cur));
				if (!satisfies(constraint, mRI.sampleFrom(2*cur))) {
					// Refutes interval left of this root
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << mRI.sampleFrom(2*cur) << " -> " << last << ".." << (2*cur));
					b.set_interval(last, 2*cur);
				}
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(2*cur+1));
				if (!satisfies(constraint, r)) {
					// Refutes root
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << r << " -> " << 2*cur+1);
					b.set(2*cur+1, 2*cur+1);
				}
				last = 2*cur + 2;
			}
			SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(last));
			if (!satisfies(constraint, mRI.sampleFrom(last))) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << mRI.sampleFrom(last) << " which is " << mRI.sampleFrom(roots.size()*2));
				// Refutes interval right of largest root
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << mRI.sampleFrom(roots.size()*2) << " -> " << last << ".." << (mRI.size()*2));
				b.set_interval(last, mRI.size()*2);
			}
			if (b.any()) {
				cover.add(c.first, b);
			}
		}
		// Handling multivariate bounds this way is unsoud: A consistent assignment may exist for these bounds,
		// but cannot be found by the assignment finder. Thus, satisfying cells may be excluded.
		// Currently, these bounds are disabled in the BaseBackend/Bookkeeping, but they may be handled using
		// the CAD.
		assert(mMVBounds.empty());
		/*
		for (const auto& c: mMVBounds) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Computing cover for " << c);
			carl::Bitset b;
			for (std::size_t i = 0; i < mRI.size() * 2 + 1; ++i) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", c << " vs " << mRI.sampleFrom(i));
				
				Model m = mModel;
				m.assign(mVar, mRI.sampleFrom(i));
				auto res = carl::model::evaluate(c, m);
				if (!res.isBool()) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", c << " is inconclusive on " << mRI.sampleFrom(i));
				} else if (!res.asBool()) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", c << " refutes " << mRI.sampleFrom(i));
					b.set(i);
				}
			}
			if (b.any()) {
				cover.add(c, b);
			}
		}
		*/
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", cover);
		return cover;
	}
	
	AssignmentOrConflict findAssignment() {
		Covering cover = computeCover();
		if (cover.conflicts()) {
			FormulasT conflict;
			cover.buildConflictingCore(conflict);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "No Assignment, built conflicting core " << conflict << " under model " << mModel);
			return conflict;
		} else {
			ModelValue assignment = selectAssignment(cover);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Assignment: " << mVar << " = " << assignment << " from interval " << cover.satisfyingInterval());
			assert(assignment.isRAN());
			if (assignment.asRAN().is_numeric()) {
				assignment = assignment.asRAN().value();
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Assignment: " << mVar << " = " << assignment);
			ModelValues res;
			res.push_back(std::make_pair(mVar,assignment));
			return res;
		}
	}
	
};

}
}
}
