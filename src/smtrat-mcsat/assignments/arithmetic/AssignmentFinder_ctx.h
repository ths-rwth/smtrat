#pragma once

#include "Covering.h"
#include "RootIndexer.h"

#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/smtrat-mcsat.h>
#include <carl-formula/model/Assignment.h>

#include <carl-arith/ran/Conversion.h>
#include <carl-arith/extended/Conversion.h>
#include <carl-arith/constraint/Conversion.h>



#include <algorithm>

namespace smtrat {
namespace mcsat {
namespace arithmetic {

using carl::operator<<;

class AssignmentFinder_ctx {
using Polynomial = carl::LPPolynomial;

private:
	typename Polynomial::ContextType m_context;
	carl::Variable m_var;
	carl::Assignment<typename Polynomial::RootType> m_assignment;
	RootIndexer<typename Polynomial::RootType> m_ri;
	/**
	 * Maps the input formula to the list of real roots and the simplified formula where m_assignment was substituted.
	 */
	std::map<FormulaT, std::pair<std::vector<typename Polynomial::RootType>, std::variant<carl::BasicConstraint<Polynomial>, carl::VariableComparison<Polynomial>>>> m_root_map;
	
	bool satisfies(const std::variant<carl::BasicConstraint<Polynomial>, carl::VariableComparison<Polynomial>>& f, const typename Polynomial::RootType& r) const {
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", f << ", " << m_assignment << ", " << m_var << ", " << r);
		auto m = m_assignment;
		m.emplace(m_var, r);
		auto res = std::visit([&](auto&& arg) { return carl::evaluate(arg, m); }, f);
		assert(!indeterminate(res));
		SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Evaluating " << f << " on " << m << " -> " << res);
		return (bool)res;
	}
	
	bool compare_assignments(std::size_t lhs, std::size_t rhs) const {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", lhs << " < " << rhs << "?");
		const auto& l = m_ri.sampleFrom(lhs);
		const auto& r = m_ri.sampleFrom(rhs);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", l << " (" << m_ri.is_root(lhs) << ") < " << r << " (" << m_ri.is_root(rhs) << ") ?");
		// this is more like z3, but performs worse:
		// if ((l.is_integer() || l.is_numeric()) && (r.is_integer() || r.is_numeric()) && (m_ri.is_root(lhs) != m_ri.is_root(rhs))) return !m_ri.is_root(lhs);
		// even the opposite performs better (but not better than not respecting samples being a root):
		// if ((l.is_integer() || l.is_numeric()) && (r.is_integer() || r.is_numeric()) && (m_ri.is_root(lhs) != m_ri.is_root(rhs))) return m_ri.is_root(lhs);
		if (carl::is_integer(l) != carl::is_integer(r)) return carl::is_integer(l);
		if (l.is_numeric() != r.is_numeric()) return l.is_numeric();
		if (carl::size(l) != carl::size(r)) return carl::size(l) < carl::size(r);
		if (carl::abs(l) != carl::abs(r)) return carl::abs(l) < carl::abs(r);
		return l < r;
	}
	
	auto select_assignment(const Covering& cover) const {
		std::vector<std::size_t> samples;
		for (auto b: cover.satisfyingSamples()) {
			samples.push_back(b);
		}
		assert(samples.size() > 0);
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Finding minimum from " << samples);
		auto min = std::min_element(samples.begin(), samples.end(), [this](auto lhs, auto rhs){ return this->compare_assignments(lhs, rhs); });
		return m_ri.sampleFrom(*min);	
	}

	bool fits_context(const FormulaT& f) {
		for (const auto& v : f.variables()) {
			if (std::find(m_context.variable_ordering().begin(), m_context.variable_ordering().end(), v) == m_context.variable_ordering().end()) {
				return false;
			}
		}
		return true;
	}
	
public:
	AssignmentFinder_ctx(const std::vector<carl::Variable>& var_order, carl::Variable var, const Model& model): m_context(var_order), m_var(var) {
		for (const auto& e : get_ran_assignment(model)) {
			m_assignment.emplace(e.first, carl::convert<typename Polynomial::RootType>(e.second));
		}
	}
	
	bool addConstraint(const FormulaT& f1) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << f1);
		if (!fits_context(f1)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f1 << " contains too many variables for context " << m_context);
			return true;
		}
		auto f = carl::convert<Polynomial>(m_context, f1.constraint().constr());
		if (f.is_trivial_true() || f.is_trivial_false()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " is constant " << f.is_trivial_true());
			return f.is_trivial_true();
		} else if (f.lhs().main_var() == m_var) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Considering univariate constraint " << f << " under " << m_assignment);
			std::vector<typename Polynomial::RootType> list;
			SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Real roots of " << f.lhs() << " in " << m_var << " w.r.t. " << m_assignment);
			auto roots = carl::real_roots(f.lhs(), m_assignment);
			if (roots.is_univariate()) {
				list = roots.roots();
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << list);
				m_ri.add(list);
				m_root_map.emplace(f1, std::move(std::make_pair(list, f)));
				return true;
			} else {
				assert(roots.is_nullified());
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Failed to compute roots because polynomial is nullified.");
				if (carl::evaluate(carl::Sign::ZERO, f.relation())) {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " simplified to true.");
					return true;
				} else {
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
					return false;
				}
			}
		} else if (m_assignment.find(f.lhs().main_var()) != m_assignment.end()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " evaluates under " << m_assignment);
			auto res = carl::evaluate(f, m_assignment);
			assert(!indeterminate(res));
			if (res) {
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Ignoring " << f << " which simplified to true.");
				return true;
			} else {
				assert(!res);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
				return false;
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Ignoring unassigned constraint " << f << " under " << m_assignment);
			return true;
		}
	}
	
	bool addMVBound(const FormulaT& f1) {
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << f1);
		if (!fits_context(f1)) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f1 << " contains too many variables for context " << m_context);
			return true;
		}
		auto f = carl::convert<Polynomial>(m_context, f1.variable_comparison());
		assert(std::get<carl::MultivariateRoot<Polynomial>>(f.value()).var() == f.var());
		if (f.var() == m_var) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " is univariate under " << m_assignment);
			auto value = carl::evaluate(std::get<carl::MultivariateRoot<Polynomial>>(f.value()), m_assignment);
			if (!value) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " is not well-defined.");
				return f.negated();
			} else {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Evaluated to " << *value);
				std::vector<typename Polynomial::RootType> list;
				list.push_back(*value);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Adding " << list << " with " << f);
				m_ri.add(list);
				m_root_map.emplace(f1, std::make_pair(std::move(list), f));
				return true;
			}
		} else if (m_assignment.find(f.var()) != m_assignment.end()) {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", f << " evaluates under " << m_assignment);
			auto res = carl::evaluate(f, m_assignment);
			if (indeterminate(res)) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " is not well-defined.");
				return f.negated();
			} else if (res) {
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", "Ignoring " << f << " which simplified to true.");
				return true;
			} else {
				assert(!res);
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Conflict: " << f << " simplified to false.");
				return false;
			}
		} else {
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Ignoring unassigned bound " << f << " under " << m_assignment);
			return true;
		}
	}
	
	Covering computeCover() {
		m_ri.process();
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", m_ri);
		Covering cover(m_ri.size() * 2 + 1);
		for (const auto& c: m_root_map) {
			carl::Bitset b;
			const auto& roots = c.second.first; // sorted
			const auto& constraint = c.second.second;
			std::size_t last = 0;
			for (const auto& r: roots) {
				std::size_t cur = m_ri[r];
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << m_ri.sampleFrom(2*cur));
				if (!satisfies(constraint, m_ri.sampleFrom(2*cur))) {
					// Refutes interval left of this root
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << m_ri.sampleFrom(2*cur) << " -> " << last << ".." << (2*cur));
					b.set_interval(last, 2*cur);
				}
				SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << m_ri.sampleFrom(2*cur+1));
				if (!satisfies(constraint, r)) {
					// Refutes root
					SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << r << " -> " << 2*cur+1);
					b.set(2*cur+1, 2*cur+1);
				}
				last = 2*cur + 2;
			}
			SMTRAT_LOG_TRACE("smtrat.mcsat.assignmentfinder", constraint << " vs " << m_ri.sampleFrom(last));
			if (!satisfies(constraint, m_ri.sampleFrom(last))) {
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << m_ri.sampleFrom(last) << " which is " << m_ri.sampleFrom(roots.size()*2));
				// Refutes interval right of largest root
				SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", constraint << " refutes " << m_ri.sampleFrom(roots.size()*2) << " -> " << last << ".." << (m_ri.size()*2));
				b.set_interval(last, m_ri.size()*2);
			}
			if (b.any()) {
				cover.add(c.first, b);
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", cover);
		return cover;
	}
	
	AssignmentOrConflict findAssignment() {
		Covering cover = computeCover();
		if (cover.conflicts()) {
			FormulasT conflict;
			cover.buildConflictingCore(conflict);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "No Assignment, built conflicting core " << conflict << " under model " << m_assignment);
			return conflict;
		} else {
			ModelValue assignment = carl::convert<RAN>(select_assignment(cover));
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Assignment: " << m_var << " = " << assignment << " from interval " << cover.satisfyingInterval());
			assert(assignment.isRAN());
			if (assignment.asRAN().is_numeric()) {
				assignment = assignment.asRAN().value();
			}
			SMTRAT_LOG_DEBUG("smtrat.mcsat.assignmentfinder", "Assignment: " << m_var << " = " << assignment);
			ModelValues res;
			res.push_back(std::make_pair(m_var,assignment));
			return res;
		}
	}
	
};

}
}
}
