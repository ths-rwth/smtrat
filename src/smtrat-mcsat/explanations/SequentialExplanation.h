#pragma once

#include "../utils/Bookkeeping.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct SequentialExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;
	template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
	boost::optional<Explanation> explain(const mcsat::Bookkeeping&, carl::Variable, const FormulasT&) const {
		SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "No explanation left.");
		return boost::none;
	}
	template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
	boost::optional<Explanation> explain(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
		auto res = std::get<N>(mBackends)(data, var, reason);
		if (res) return res;
		return explain<N+1>(data, var, reason);
	}
public:
	boost::optional<Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
		return explain<0>(data, var, reason);
	}
};

} // namespace mcsat
} // namespace smtrat
