#include "BooleanEncoding.h"
#include "ParserState.h"
#include "Conversions.h"
#include "FunctionInstantiator.h"

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

namespace smtrat {
namespace parser {

	struct EncodingInstantiator: public IndexedFunctionInstantiator {
		bool operator()(const std::vector<std::size_t>& indices, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
			std::vector<FormulaT> args;
			if (!convert(arguments, args)) return false;
			return apply(indices, args, result, errors);
		}
		virtual bool apply(const std::vector<std::size_t>& indices, const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& errors) const = 0;
	};

	void at_most_k_helper(size_t k, const std::vector<FormulaT>& set, FormulasT& working, long long int prev_idx, FormulasT& results) {
		for (size_t i = prev_idx+1; i < set.size(); i++) {
			working.push_back(set[i].negated());
			if (working.size() == k+1) {
				results.emplace_back(carl::FormulaType::OR, working);
			} else {
				at_most_k_helper(k, set, working, i, results);
			}
			working.pop_back();
		}
	}
	FormulaT at_most_k(size_t k, const std::vector<FormulaT>& set) {
		if (k >= set.size()) {
			return FormulaT(carl::FormulaType::TRUE);
		} else {
			FormulasT working;
			FormulasT results;
			at_most_k_helper(k, set, working, -1, results);
			return FormulaT(carl::FormulaType::AND, std::move(results));
		}
	}
	
	struct AtMostInstantiator: public EncodingInstantiator {
		bool apply(const std::vector<std::size_t>& indices, const std::vector<FormulaT>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() == 0) {
				errors.next() << "The operator \"at-most\" expects at least one argument.";
				return false;
			}
			if (indices.size() != 1) {
				errors.next() << "The operator \"at-most\" expects exactly one index.";
				return false;
			}

			result = at_most_k(indices[0], arguments); // TODO better encoding, see http://www.cs.toronto.edu/~fbacchus/csc2512/at_most_k.pdf
			return true;
		}
	};

	BooleanEncodingTheory::BooleanEncodingTheory(ParserState* state): AbstractTheory(state) {
		state->registerFunction("at-most", new AtMostInstantiator());
	}

}
}
