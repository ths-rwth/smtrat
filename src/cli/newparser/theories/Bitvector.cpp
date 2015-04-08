#include "Bitvector.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	void BitvectorTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("Bool", sm.interpretedSort(carl::VariableType::VT_BOOL));
	}
	
	bool BitvectorTheory::convertTerm(const types::TermType& term, types::BVTerm& result) {
		if (boost::get<types::BVTerm>(&term) != nullptr) {
			result = boost::get<types::BVTerm>(term);
			return true;
		} else if (boost::get<carl::BVVariable>(&term) != nullptr) {
			result = types::BVTerm(carl::BVTermType::VARIABLE, boost::get<carl::BVVariable>(term));
			return true;
		} else {
			return false;
		}
	}

	bool BitvectorTheory::convertArguments(const std::vector<types::TermType>& arguments, std::vector<types::BVTerm>& result, TheoryError& errors) {
		result.clear();
		for (std::size_t i = 0; i < arguments.size(); i++) {
			types::BVTerm res;
			if (!convertTerm(arguments[i], res)) {
				errors.next() << "Operator expects arguments to be a bitvector, but argument " << (i+1) << " is not: \"" << arguments[i] << "\".";
				return false;
			}
			result.push_back(res);
		}
		return true;
	}

	BitvectorTheory::BitvectorTheory(ParserState* state): AbstractTheory(state) {
	}

	bool BitvectorTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		if (!sm.isInterpreted(sort)) return false;
		switch (sm.interpretedType(sort)) {
			case carl::VariableType::VT_BITVECTOR: {
				assert(state->isSymbolFree(name));
				carl::Variable v = carl::freshVariable(name, carl::VariableType::VT_BITVECTOR);
				state->variables[name] = carl::BVVariable(v, sort);
				return true;
			}
			default:
				return false;
		}
	}

	bool BitvectorTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		types::BVTerm thent;
		types::BVTerm elset;
		if (!convertTerm(thenterm, thent)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!convertTerm(elseterm, elset)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		//result = FormulaT(carl::FormulaType::ITE, ifterm, thenf, elsef);
		return false;
	}

	bool BitvectorTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		if (identifier.symbol == "=") {
			if (arguments.size() == 2) {
				std::vector<types::BVTerm> args;
				if (!convertArguments(arguments, args, errors)) return false;
				result = types::BVTerm(carl::BVTermType::EQ, args[0], args[1]);
				return true;
			}
			errors.next() << "Operator \"" << identifier << "\" expects exactly two arguments, but got " << arguments.size() << ".";
			return false;
		}
		errors.next() << "Invalid operator \"" << identifier << "\".";
		return false;
	}

}
}
