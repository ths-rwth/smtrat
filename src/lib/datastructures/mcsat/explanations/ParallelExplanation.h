#pragma once

#include "../common.h"
#include "../Bookkeeping.h"

#include <carl/util/tuple_util.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct ParallelExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;
public:
	boost::optional<FormulaT> operator()(const mcsat::Bookkeeping& data, const std::vector<carl::Variable>& variableOrdering, carl::Variable var, const FormulasT& reason, const FormulaT& implication) const {
		auto F = [&](const auto& expl){
			auto r = expl(data, variableOrdering, var, reason, implication);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Got explanation " << r);
			return r;
		};
		auto res = carl::tuple_foreach(F, mBackends);
		carl::tuple_foreach(
			[&res](const auto& ref){
				assert(std::get<0>(res) == ref);
				return true;
			},
			mBackends
		);
		return std::get<0>(res);
	}
};

} // namespace mcsat
} // namespace smtrat
