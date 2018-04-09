#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

#include <carl/util/tuple_util.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct SequentialExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;
	template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
	boost::optional<FormulaT> explain(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "No explanation left.");
		return boost::none;
	}
	template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
	boost::optional<FormulaT> explain(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		auto res = std::get<N>(mBackends)(data, variableOrdering, var, reason, implication);
		if (res) return res;
		return explain<N+1>(data, variableOrdering, var, reason, implication);
	}
public:
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		return explain<0>(data, variableOrdering, var, reason, implication);
	}
	
};

} // namespace mcsat
} // namespace smtrat
