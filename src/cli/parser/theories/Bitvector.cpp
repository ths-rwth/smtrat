#include "Bitvector.h"
#include "ParserState.h"
#include "Conversions.h"
#include "FunctionInstantiator.h"

#define BOOST_SPIRIT_USE_PHOENIX_V3
#include <boost/spirit/include/qi.hpp>

namespace smtrat {
namespace parser {
	
	struct BitvectorInstantiator: public FunctionInstantiator {
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
	struct IndexedBitvectorInstantiator: public IndexedFunctionInstantiator {
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
			}
			result = types::BVTerm(type, arguments[0], indices[0]);
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

	BitvectorTheory::BitvectorTheory(ParserState* state): AbstractTheory(state) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		this->bvSort = sm.addSort("BitVec", carl::VariableType::VT_UNINTERPRETED);
		sm.makeSortIndexable(this->bvSort, 1, carl::VariableType::VT_BITVECTOR);

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
		state->registerFunction("bvcomp", new BinaryBitvectorInstantiator<carl::BVTermType::EQ>());
		state->registerFunction("bvshl", new BinaryBitvectorInstantiator<carl::BVTermType::LSHIFT>());
		state->registerFunction("bvlshr", new BinaryBitvectorInstantiator<carl::BVTermType::RSHIFT_LOGIC>());
		state->registerFunction("bvashr", new BinaryBitvectorInstantiator<carl::BVTermType::RSHIFT_ARITH>());
		
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

	bool BitvectorTheory::declareVariable(const std::string& name, const carl::Sort& sort, types::VariableType& result, TheoryError& errors) {
		carl::SortManager& sm = carl::SortManager::getInstance();
		switch (sm.getType(sort)) {
			case carl::VariableType::VT_BITVECTOR: {
				assert(state->isSymbolFree(name));
				if ((sm.getIndices(sort) == nullptr) || (sm.getIndices(sort)->size() != 1)) {
					errors.next() << "The sort \"" << sort << "\" should have a single index, being the bit size.";
					return false;
				}
				carl::Variable v = carl::freshVariable(name, carl::VariableType::VT_BITVECTOR);
				carl::BVVariable bvv = carl::BVVariable(v, sort);
				state->variables[name] = bvv;
				result = bvv;
				return true;
			}
			default:
				errors.next() << "The requested sort is not a bitvector sort but \"" << sort << "\".";
				return false;
		}
	}

	struct BitvectorConstantParser: public qi::grammar<std::string::const_iterator, Integer()> {
		BitvectorConstantParser(): BitvectorConstantParser::base_type(main, "bitvector literal") {
			main = "bv" > number;
		}
		qi::uint_parser<Integer,10,1,-1> number;
	    qi::rule<std::string::const_iterator, Integer()> main;
	};
	
	bool BitvectorTheory::resolveSymbol(const Identifier& identifier, types::TermType& result, TheoryError& errors) {
		Integer integer;
		const std::string& s = identifier.symbol;
		if (qi::parse(s.begin(), s.end(), BitvectorConstantParser(), integer)) {
			if (identifier.indices == nullptr) {
				errors.next() << "Found a possible bitvector symbol \"" << identifier << "\" but no bit size was specified.";
				return false;
			}
			if (identifier.indices->size() != 1) {
				errors.next() << "Found a possible bitvector symbol \"" << identifier << "\" but did not find a single index specifying the bit size.";
				return false;
			}
			std::size_t bitsize = identifier.indices->at(0);
			carl::BVValue value(bitsize, integer);
			result = types::BVTerm(carl::BVTermType::CONSTANT, value);
			return true;
		}
		return false;
	}

	bool BitvectorTheory::handleITE(const FormulaT& ifterm, const types::TermType& thenterm, const types::TermType& elseterm, types::TermType& result, TheoryError& errors) {
		types::BVTerm thent;
		types::BVTerm elset;
		if (!termConverter(thenterm, thent)) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thenterm << "\" is unsupported.";
			return false;
		}
		if (!termConverter(elseterm, elset)) {
			errors.next() << "Failed to construct ITE, the else-term \"" << elseterm << "\" is unsupported.";
			return false;
		}
		if (thent.width() != elset.width()) {
			errors.next() << "Failed to construct ITE, the then-term \"" << thent << "\" and the else-term \"" << elset << "\" have different widths.";
			return false;
		}
		if (ifterm.isTrue()) { result = thent; return true; }
		if (ifterm.isFalse()) { result = elset; return true; }
		carl::SortManager& sm = carl::SortManager::getInstance();
		carl::Variable var = carl::freshVariable(carl::VariableType::VT_BITVECTOR);
		state->artificialVariables.emplace_back(var);
		carl::BVVariable bvvar(var, sm.index(this->bvSort, {thent.width()}));
		state->auxiliary_variables.insert(bvvar);
		types::BVTerm vart = types::BVTerm(carl::BVTermType::VARIABLE, bvvar);

		FormulaT consThen = FormulaT(types::BVConstraint::create(carl::BVCompareRelation::EQ, vart, thent));
		FormulaT consElse = FormulaT(types::BVConstraint::create(carl::BVCompareRelation::EQ, vart, elset));

		state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IMPLIES, {ifterm, consThen}));
		state->global_formulas.emplace_back(FormulaT(carl::FormulaType::IMPLIES, {!ifterm, consElse}));
		result = vart;
		return true;
	}
	bool BitvectorTheory::handleDistinct(const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		std::vector<carl::BVTerm> args;
		if (!vectorConverter(arguments, args, errors)) return false;
		result = expandDistinct(args, [](const carl::BVTerm& a, const carl::BVTerm& b){
			return FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::NEQ, a, b));
		});
		return true;
	}

	bool BitvectorTheory::instantiate(const types::VariableType& var, const types::TermType& replacement, types::TermType& subject, TheoryError& errors) {
		carl::BVVariable v;
		conversion::VariantConverter<carl::BVVariable> c;
		if (!c(var, v)) {
			errors.next() << "The variable is not a bitvector variable.";
			return false;
		}
		carl::BVTerm repl;
		if (!termConverter(replacement, repl)) {
			errors.next() << "Could not convert argument \"" << replacement << "\" to a bitvector term.";
			return false;
		}
		Instantiator<carl::BVVariable, carl::BVTerm> instantiator;
		return instantiator.instantiate(v, repl, subject);
	}
	bool BitvectorTheory::refreshVariable(const types::VariableType& var, types::VariableType& subject, TheoryError& errors) {
		carl::BVVariable v;
		conversion::VariantConverter<carl::BVVariable> c;
		if (!c(var, v)) {
			errors.next() << "The variable is not a bitvector variable.";
			return false;
		}
		subject = carl::BVVariable(carl::freshVariable(carl::VariableType::VT_BITVECTOR), v.sort());
		return true;
		
	}
	bool BitvectorTheory::functionCall(const Identifier& identifier, const std::vector<types::TermType>& arguments, types::TermType& result, TheoryError& errors) {
		if (identifier.symbol == "=") {
			if (arguments.size() == 2) {
				std::vector<types::BVTerm> args;
				if (!vectorConverter(arguments, args, errors)) return false;
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
