#pragma once

namespace smtrat {
namespace mcsat {

template<typename... Backends>
class MultiBackend {

public:
	using B = std::tuple<Backends...>;
	B mBackends;

	template<typename... Backends2>
	friend std::ostream& operator<<(std::ostream& os, const MultiBackend<Backends2...>& backends) {
		auto output = carl::tuple_foreach(
			[&os](const auto& b) { return operator<<(os, b); },
			backends.mBackends);
		return std::get<0>(output);
	}

	void pushConstraint(const FormulaT& f) {
		carl::tuple_foreach(
			[f](auto& b) { b.pushConstraint(f); return true; },
			mBackends);
	}

	void popConstraint(const FormulaT& f) {
		carl::tuple_foreach(
			[f](auto& b) { b.popConstraint(f); return true; },
			mBackends);
	}

	void pushAssignment(carl::Variable v, const ModelValue& mv, const FormulaT& f) {
		carl::tuple_foreach(
			[v, mv, f](auto& b) { b.pushAssignment(v, mv, f); return true; },
			mBackends);
	}

	void popAssignment(carl::Variable v) {
		carl::tuple_foreach(
			[v](auto& b) { b.popAssignment(v); return true; },
			mBackends);
	}

	const auto& getModel() const {
		auto models = carl::tuple_foreach(
			[](const auto& b) { return b.getModel(); },
			mBackends);
		return std::get<0>(models);
	}

	auto findAssignment(carl::Variable var) const { //AssignmentFinder::AssignmentOrConflict
		auto assignments = carl::tuple_foreach(
			[var](const auto& b) { return b.findAssignment(var); },
			mBackends);
		return std::get<0>(assignments);
	}

	boost::optional<FormulasT> isInfeasible(carl::Variable var, const FormulaT& f) {
		auto infeasible = carl::tuple_foreach(
			[var, f](auto& b) { return b.isInfeasible(var, f); },
			mBackends);
		return std::get<0>(infeasible);
	}

	FormulaT explain(carl::Variable var, const FormulasT& reason, const FormulaT& implication) {
		auto expl = carl::tuple_foreach(
			[var, reason, implication](auto& b) { return b.explain(var, reason, implication); },
			mBackends);
		return std::get<0>(expl);
	}
};

struct MultiBackendSettings1 {
	using BackendType = MultiBackend<nlsat::NLSAT>;
};

} // namespace mcsat
} // namespace smtrat
