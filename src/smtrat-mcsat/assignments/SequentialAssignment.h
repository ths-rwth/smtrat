#pragma once

#include "../utils/Bookkeeping.h"

#include <carl/util/tuple_util.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct SequentialAssignment {
private:
	using B = std::tuple<Backends...>;
	B mBackends;
	template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
	boost::optional<AssignmentOrConflict> findAssignment(const mcsat::Bookkeeping& data, carl::Variable var) const {
		SMTRAT_LOG_ERROR("smtrat.mcsat.assignment", "No explanation left.");
		return boost::none;
	}
	template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
	boost::optional<AssignmentOrConflict> findAssignment(const mcsat::Bookkeeping& data, carl::Variable var) const {
		auto res = std::get<N>(mBackends)(data, var);
		if (res) return res;
		return findAssignment<N+1>(data, var);
	}
public:
	boost::optional<AssignmentOrConflict> operator()(const mcsat::Bookkeeping& data, carl::Variable var) const {
		return findAssignment<0>(data, var);
	}
	
};

} // namespace mcsat
} // namespace smtrat
