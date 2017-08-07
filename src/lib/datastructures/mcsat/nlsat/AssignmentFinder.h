#pragma once

#include "Covering.h"
#include "RootIndexer.h"

#include <boost/variant.hpp>

namespace smtrat {
namespace nlsat {

class AssignmentFinder {
public:
	using RAN = carl::RealAlgebraicNumber<Rational>;
	using AssignmentOrConflict = boost::variant<ModelValue,FormulasT>;
private:
	carl::Variable mVar;
	const Model& mModel;
	RootIndexer mRI;
	std::map<FormulaT, std::pair<std::vector<RAN>, FormulaT>> mRootMap;
	
	/// Checks whether a formula is univariate, meaning it contains mVar and only variables from mModel otherwise.
	bool isUnivariate(const FormulaT& f) const {
		carl::Variables vars;
		f.arithmeticVars(vars);
		auto it = vars.find(mVar);
		if (it == vars.end()) return false;
		vars.erase(it);
		return mModel.contains(vars);
	}
	bool satisfies(const FormulaT& f, const RAN& r) const {
		SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", f << ", " << mModel << ", " << mVar << ", " << r);
		Model m = mModel;
		m.assign(mVar, r);
		SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", r);
		auto res = carl::model::evaluate(f, m);
		SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", r);
		SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", "Evaluating " << f << " -> " << res);
		if (!res.isBool()) std::exit(75);
		assert(res.isBool());
		return res.asBool();
	}
public:
	AssignmentFinder(carl::Variable var, const Model& model): mVar(var), mModel(model) {}
	
	bool addConstraint(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::CONSTRAINT);
		if (!isUnivariate(f)) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Ignoring non-univariate constraint " << f);
			return true;
		}
		FormulaT fnew(carl::model::substitute(f, mModel));
		std::vector<RAN> list;
		if (fnew.getType() == carl::FormulaType::CONSTRAINT) {
			const auto& poly = fnew.constraint().lhs();
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Real roots of " << poly << " in " << mVar);
			auto roots = carl::model::tryRealRoots(poly, mVar, mModel);
			if (roots) {
				list = *roots;
			} else {
				SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Failed to compute roots, or polynomial becomes zero.");
			}
		} else if (fnew.getType() == carl::FormulaType::TRUE) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Ignoring " << f << " which simplified to true.");
		} else {
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Constraint " << f << " simplified to false.");
			return false;
		}
		
		mRI.add(list);
		mRootMap.emplace(f, std::make_pair(std::move(list), fnew));
		return true;
	}
	
	void addMVBound(const FormulaT& f) {
		assert(f.getType() == carl::FormulaType::VARCOMPARE);
		if (!isUnivariate(f)) {
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Ignoring non-univariate bound " << f);
			return;
		}
		FormulaT fnew(carl::model::substitute(f, mModel));
		assert(fnew.getType() == carl::FormulaType::VARCOMPARE);
		ModelValue value = fnew.variableComparison().value();
		if (value.isSubstitution()) {
			// Prevent memory error due to deallocation of shared_ptr before copying value from shared_ptr.
			auto res = value.asSubstitution()->evaluate(mModel);
			value = res;
		}
		if (!value.isRational() && !value.isRAN()) return;
		std::vector<RAN> list;
		if (value.isRational()) list.emplace_back(value.asRational());
		else list.push_back(value.asRAN().changeVariable(mVar));
		mRI.add(list);
		mRootMap.emplace(f, std::make_pair(std::move(list), fnew));
	}
	
	Covering computeCover() {
		mRI.process();
		Covering cover(mRI.size() * 2 + 1);
		for (const auto& c: mRootMap) {
			carl::Bitset b;
			const auto& roots = c.second.first;
			const auto& constraint = c.second.second;
			std::size_t last = 0;
			for (const auto& r: roots) {
				std::size_t cur = mRI[r];
				SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(2*cur));
				if (!satisfies(constraint, mRI.sampleFrom(2*cur))) {
					// Refutes interval left of this root
					SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " refutes " << mRI.sampleFrom(2*cur) << " -> " << last << ".." << (2*cur));
					b.set_interval(last, 2*cur);
				}
				SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(2*cur+1));
				SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", mRI);
				if (!satisfies(constraint, r)) {
					// Refutes root
					SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " refutes " << r << " -> " << 2*cur+1);
					b.set(2*cur+1, 2*cur+1);
				}
				SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", mRI);
				last = 2*cur + 2;
			}
			SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " vs " << mRI.sampleFrom(last));
			if (!satisfies(constraint, mRI.sampleFrom(last))) {
				// Refutes interval right of largest root
				SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", constraint << " refutes " << mRI.sampleFrom(roots.size()*2) << " -> " << last << ".." << (mRI.size()*2));
				b.set_interval(last, mRI.size()*2);
			}
			cover.add(c.first, b);
		}
		SMTRAT_LOG_TRACE("smtrat.nlsat.assignmentfinder", cover);
		return cover;
	}
	
	AssignmentOrConflict findAssignment() {
		Covering cover = computeCover();
		if (cover.conflicts()) {
			FormulasT conflict;
			cover.buildConflictingCore(conflict);
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "No Assignment, built conflicting core " << conflict << " under model " << mModel);
			return conflict;
		} else {
			ModelValue assignment = mRI.sampleFrom(cover.satisfyingInterval());
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Assignment: " << mVar << " = " << assignment);
			assert(assignment.isRAN());
			if (assignment.asRAN().isNumeric()) {
				assignment = assignment.asRAN().value();
			}
			SMTRAT_LOG_DEBUG("smtrat.nlsat.assignmentfinder", "Assignment: " << mVar << " = " << assignment);
			return assignment;
		}
	}
	
};

}
}
