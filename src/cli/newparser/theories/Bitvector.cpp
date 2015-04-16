#include "Bitvector.h"
#include "ParserState.h"

namespace smtrat {
namespace parser {
	
	struct BitvectorInstantiator: public types::FunctionInstantiator {
		bool operator()(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
			std::vector<types::BVTerm> args;
			if (!convert(arguments, args)) {
				errors.next() << "Failed to convert arguments.";
				return false;
			}
			return apply(args, result, errors);
		}
		virtual bool apply(const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const = 0;
	};
	struct IndexedBitvectorInstantiator: public types::IndexedFunctionInstantiator {
		bool operator()(const std::vector<std::size_t>& indices, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) const {
			std::vector<types::BVTerm> args;
			if (!convert(arguments, args)) {
				errors.next() << "Failed to convert arguments.";
				return false;
			}
			return apply(indices, args, result, errors);
		}
		virtual bool apply(const std::vector<std::size_t>& indices, const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const = 0;
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
	template<carl::BVCompareRelation type>
	struct BitvectorRelationInstantiator: public BitvectorInstantiator {
		bool apply(const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 2) {
				errors.next() << "The operator \"" << type << "\" expects exactly two arguments.";
				return false;
			}
			result = FormulaT(types::BVConstraint::create(type, arguments[0], arguments[1]));
			return true;
		}
	};
	template<carl::BVTermType type>
	struct SingleIndexBitvectorInstantiator: public IndexedBitvectorInstantiator {
		bool apply(const std::vector<std::size_t>& indices, const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 1) {
				errors.next() << "The operator \"" << type << "\" expects exactly one argument.";
				return false;
			}
			if (indices.size() != 1) {
				errors.next() << "The operator \"" << type << "\" expects exactly one index.";
				return false;
			result = types::BVTerm(type, arguments[0], indices[0]);
			}
			return true;
		}
	};
	struct ExtractBitvectorInstantiator: public IndexedBitvectorInstantiator {
		bool apply(const std::vector<std::size_t>& indices, const std::vector<types::BVTerm>& arguments, types::TermType& result, TheoryError& errors) const {
			if (arguments.size() != 1) {
				errors.next() << "The operator \"extract\" expects exactly one argument.";
				return false;
			}
			if (indices.size() != 2) {
				errors.next() << "The operator \"extract\" expects exactly two indices.";
				return false;
			}
			result = types::BVTerm(carl::BVTermType::EXTRACT, arguments[0], indices[0], indices[1]);
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

		state->registerFunction("concat", new BinaryBitvectorInstantiator<carl::BVTermType::CONCAT>());
		state->registerFunction("extract", new ExtractBitvectorInstantiator());
		
		state->registerFunction("bvnot", new UnaryBitvectorInstantiator<carl::BVTermType::NOT>());
		state->registerFunction("bvneg", new UnaryBitvectorInstantiator<carl::BVTermType::NEG>());
		
		state->registerFunction("bvand", new BinaryBitvectorInstantiator<carl::BVTermType::AND>());
		state->registerFunction("bvor", new BinaryBitvectorInstantiator<carl::BVTermType::OR>());
		state->registerFunction("bvxor", new BinaryBitvectorInstantiator<carl::BVTermType::XOR>());
		state->registerFunction("bvnand", new BinaryBitvectorInstantiator<carl::BVTermType::NAND>());
		state->registerFunction("bvnor", new BinaryBitvectorInstantiator<carl::BVTermType::NOR>());
		state->registerFunction("bvxnor", new BinaryBitvectorInstantiator<carl::BVTermType::XNOR>());
		state->registerFunction("bvadd", new BinaryBitvectorInstantiator<carl::BVTermType::ADD>());
		state->registerFunction("bvplus", new BinaryBitvectorInstantiator<carl::BVTermType::ADD>());
		state->registerFunction("bvsub", new BinaryBitvectorInstantiator<carl::BVTermType::SUB>());
		state->registerFunction("bvmul", new BinaryBitvectorInstantiator<carl::BVTermType::MUL>());
		state->registerFunction("bvudiv", new BinaryBitvectorInstantiator<carl::BVTermType::DIV_U>());
		state->registerFunction("bvsdiv", new BinaryBitvectorInstantiator<carl::BVTermType::DIV_S>());
		state->registerFunction("bvurem", new BinaryBitvectorInstantiator<carl::BVTermType::MOD_U>());
		state->registerFunction("bvsrem", new BinaryBitvectorInstantiator<carl::BVTermType::MOD_S1>());
		state->registerFunction("bvsmod", new BinaryBitvectorInstantiator<carl::BVTermType::MOD_S2>());
		state->registerFunction("bvshl", new BinaryBitvectorInstantiator<carl::BVTermType::LSHIFT>());
		state->registerFunction("bvlshr", new BinaryBitvectorInstantiator<carl::BVTermType::RSHIFT_LOGIC>());
		
		state->registerFunction("rotate_left", new SingleIndexBitvectorInstantiator<carl::BVTermType::LROTATE>());
		state->registerFunction("rotate_right", new SingleIndexBitvectorInstantiator<carl::BVTermType::RROTATE>());
		state->registerFunction("zero_extend", new SingleIndexBitvectorInstantiator<carl::BVTermType::EXT_U>());
		state->registerFunction("sign_extend", new SingleIndexBitvectorInstantiator<carl::BVTermType::EXT_S>());
		state->registerFunction("repeat", new SingleIndexBitvectorInstantiator<carl::BVTermType::REPEAT>());
		
		state->registerFunction("bvult", new BitvectorRelationInstantiator<carl::BVCompareRelation::ULT>());
		state->registerFunction("bvule", new BitvectorRelationInstantiator<carl::BVCompareRelation::ULE>());
		state->registerFunction("bvugt", new BitvectorRelationInstantiator<carl::BVCompareRelation::UGT>());
		state->registerFunction("bvuge", new BitvectorRelationInstantiator<carl::BVCompareRelation::UGE>());
		state->registerFunction("bvslt", new BitvectorRelationInstantiator<carl::BVCompareRelation::SLT>());
		state->registerFunction("bvsle", new BitvectorRelationInstantiator<carl::BVCompareRelation::SLE>());
		state->registerFunction("bvsgt", new BitvectorRelationInstantiator<carl::BVCompareRelation::SGT>());
		state->registerFunction("bvsge", new BitvectorRelationInstantiator<carl::BVCompareRelation::SGE>());
	}

	bool BitvectorTheory::declareVariable(const std::string& name, const carl::Sort& sort) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
			case carl::VariableType::VT_BITVECTOR: {
				assert(state->isSymbolFree(name));
				carl::Variable v = carl::freshVariable(name, carl::VariableType::VT_BITVECTOR);
				state->variables[name] = types::BVTerm(carl::BVTermType::VARIABLE, carl::BVVariable(v, sort));
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
				result = FormulaT(types::BVConstraint::create(carl::BVCompareRelation::EQ, args[0], args[1]));
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
