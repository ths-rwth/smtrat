#pragma once

#include "../utils/Bookkeeping.h"

#include <carl-common/util/tuple_util.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct SequentialAssignment {
private:
	using B = std::tuple<Backends...>;
	B mBackends;
	template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
	std::optional<AssignmentOrConflict> findAssignment(const mcsat::Bookkeeping&, carl::Variable) const {
		SMTRAT_LOG_ERROR("smtrat.mcsat.assignment", "No assignment finder left.");
		return std::nullopt;
	}
	template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
	std::optional<AssignmentOrConflict> findAssignment(const mcsat::Bookkeeping& data, carl::Variable var) const {
		auto res = std::get<N>(mBackends)(data, var);
		if (res) return res;
		return findAssignment<N+1>(data, var);
	}

	template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
	bool active(const mcsat::Bookkeeping&, const FormulaT&) const {
		SMTRAT_LOG_ERROR("smtrat.mcsat.assignment", "No assignment finder left.");
		return true;
	}
	template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
	bool active(const mcsat::Bookkeeping& data, const FormulaT& f) const {
		auto res = std::get<N>(mBackends).active(data, f);
		return res && active<N+1>(data, f);
	}
public:
	std::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		return findAssignment<0>(data, var);
	}

	bool active(const mcsat::Bookkeeping& data, const FormulaT& f) const {
		return active<0>(data, f);
	}
	
};

} // namespace mcsat
} // namespace smtrat
