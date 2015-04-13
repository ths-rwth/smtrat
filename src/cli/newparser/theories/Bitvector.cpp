#include "Bitvector.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	
	struct BitvectorInstantiator: public types::FunctionInstantiator {
		bool operator()(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
			std::vector<types::BVTerm> args;
			if (!convert(arguments, args)) return false;
			return apply(args, result, errors);
		}
		virtual bool apply(const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const = 0;
	};
	template<carl::BVTermType type>
	struct UnaryBitvectorInstantiator: public BitvectorInstantiator {
		bool apply(const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 1) {
				errors.next() << "The operator \"" << type << "\" expects exactly one argument.";
				return false;
			}
			result = types::BVTerm(type, arguments[0]);
			return true;
		}
	};
	template<carl::BVTermType type>
	struct BinaryBitvectorInstantiator: public BitvectorInstantiator {
		bool apply(const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 2) {
				errors.next() << "The operator \"" << type << "\" expects exactly two arguments.";
				return false;
			}
			result = types::BVTerm(type, arguments[0], arguments[1]);
			return true;
		}
	};
	
	void BitvectorTheory::addSimpleSorts(qi::symbols<char, carl::Sort>& sorts) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		sorts.add("BitVec", sm.getInterpreted(carl::VariableType::VT_BOOL));
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
		carl::SortManager& sm = carl::SortManager::getInstance();
		carl::Sort bv = sm.addSort("BitVec", carl::VariableType::VT_UNINTERPRETED);
		sm.makeSortIndexable(bv, 1, carl::VariableType::VT_BITVECTOR);

		state->registerFunction("bvnot", new UnaryBitvectorInstantiator<carl::BVTermType::NOT>());
		//state->registerFunction("bvslt", new BinaryBitvectorInstantiator<carl::BVTermType::NOT>());
	}

	bool BitvectorTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
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

	struct BitvectorConstantParser: public qi::grammar<std::string::const_iterator, Rational()> {
		BitvectorConstantParser(): BitvectorConstantParser::base_type(main, "bitvector literal") {
			main = "bv" > number;
		}
		qi::uint_parser<Integer,10,1,-1> number;
	    qi::rule<std::string::const_iterator, Rational()> main;
	};
	
	bool BitvectorTheory::resolveSymbol(const Identifier& identifier, types::TermType& result, TheoryError& errors) {
		Rational r;
		const std::string& s = identifier.symbol;
		if (qi::parse(s.begin(), s.end(), BitvectorConstantParser(), r)) {
			if (identifier.indices == nullptr) {
				errors.next() << "Found a possible bitvector symbol \"" << identifier << "\" but no bit size was specified.";
				return false;
			}
			if (identifier.indices->size() != 1) {
				errors.next() << "Found a possible bitvector symbol \"" << identifier << "\" but did not find a single index specifying the bit size.";
				return false;
			}
			std::size_t bitsize = identifier.indices->at(0);
			if (bitsize <= sizeof(std::size_t) * CHAR_BIT) {
				carl::BVValue value(bitsize, carl::toInt<std::size_t>(r));
				result = types::BVTerm(carl::BVTermType::CONSTANT, value);
				return true;
			} else {
				errors.next() << "Bitvector constant was larger than " << sizeof(std::size_t) << " bits.";
				return false;
			}
		}
		return false;
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
