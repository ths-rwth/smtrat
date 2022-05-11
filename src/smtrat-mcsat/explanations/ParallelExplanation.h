#pragma once

#include "../utils/Bookkeeping.h"

#include <carl-common/util/tuple_util.h>
#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

template<typename... Backends>
struct ParallelExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;

public:
	std::optional<Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, bool force_use_core) const {
		auto F = [&](const auto& expl) {
			auto r = expl(data, var, reason, force_use_core);
			SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Got explanation " << r);
			return r;
		};
		auto res = carl::tuple_foreach(F, mBackends);
		carl::tuple_foreach(
			[&res](const auto& ref) {
				assert(std::get<0>(res) == ref);
				return true;
			},
			mBackends);
		return std::get<0>(res);
	}
};

} // namespace mcsat
} // namespace smtrat
