#include "ParserState.h"

namespace smtrat {
namespace parser {
	
bool ParserState::checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, FormulaT>& boolAssignments, std::map<carl::Variable, Poly>& theoryAssignments) {
	if (types.size() != args.size()) {
		this->handler->error() << "The number of arguments for \"" << name << "\" does not match its declaration.";
		return false;
	}
	for (unsigned id = 0; id < types.size(); id++) {
		ExpressionType type = TypeOfTerm::get(types[id]);
		if (type != TypeOfTerm::get(args[id])) {
			this->handler->error() << "The type of argument " << (id+1) << " for \"" << name << "\" did not match the declaration.";
			return false;
		}
		if (type == ExpressionType::BOOLEAN) {
			boolAssignments[types[id]] = boost::get<FormulaT>(args[id]);
		} else {
			theoryAssignments[types[id]] = boost::get<Poly>(args[id]);
		}
	}
	return true;
}
	
bool ParserState::isSymbolFree(const std::string& name, bool output) {
	std::stringstream out;
	if (name == "true" || name == "false") out << "'" << name << "' is a reserved keyword.";
	else if (this->var_bool.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean variable.";
	else if (this->var_theory.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory variable.";
	else if (this->var_uninterpreted.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted variable.";
	else if (this->bind_bool.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean binding.";
	else if (this->bind_theory.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory binding.";
	else if (this->bind_uninterpreted.sym.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted binding.";
	else if (this->funmap_bool.find(name) != nullptr) out << "'" << name << "' has already been defined as a boolean function.";
	else if (this->funmap_theory.find(name) != nullptr) out << "'" << name << "' has already been defined as a theory funtion.";
	else if (this->funmap_ufbool.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function of boolean return type.";
	else if (this->funmap_uftheory.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function of theory return type.";
	else if (this->funmap_uf.find(name) != nullptr) out << "'" << name << "' has already been defined as an uninterpreted function.";
	else return true;
	if (output) this->handler->error() << out.str();
	return false;
}

FormulaT ParserState::applyBooleanFunction(const BooleanFunction& f, const Arguments& args) {
	std::map<carl::Variable, FormulaT> boolAssignments;
	std::map<carl::Variable, Poly> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
		return FormulaT();
	}
	return std::get<2>(f).substitute(boolAssignments, theoryAssignments);
}
Poly ParserState::applyTheoryFunction(const TheoryFunction& f, const Arguments& args) {
	std::map<carl::Variable, FormulaT> boolAssignments;
	std::map<carl::Variable, Poly> theoryAssignments;
	if (!checkArguments(std::get<0>(f), std::get<1>(f), args, boolAssignments, theoryAssignments)) {
		return smtrat::Poly();
	}
	return std::get<2>(f).substitute(theoryAssignments);
}
carl::UFInstance ParserState::applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
	std::vector<carl::UVariable> vars;
	for (auto v: args) {
		auto it = mUninterpretedArguments.find(v);
		if (it != mUninterpretedArguments.end()) {
			vars.push_back(it->second);
			continue;
		} else if (FormulaT* f = boost::get<FormulaT>(&v)) {
			carl::Variable tmp = carl::freshBooleanVariable();
			vars.push_back(carl::UVariable(tmp));
			mUninterpretedEqualities.insert(FormulaT(carl::FormulaType::IFF, FormulaT(tmp), *f));
		} else if (Poly* p = boost::get<Poly>(&v)) {
			carl::Variable tmp = carl::freshRealVariable();
			vars.push_back(carl::UVariable(tmp));
			mUninterpretedEqualities.insert(FormulaT(*p - tmp, carl::Relation::EQ));
		} else if (carl::UVariable* uv = boost::get<carl::UVariable>(&v)) {
			vars.push_back(*uv);
		} else if (carl::UFInstance* uf = boost::get<carl::UFInstance>(&v)) {
			carl::Variable tmp = carl::freshUninterpretedVariable();
			vars.push_back(carl::UVariable(tmp, uf->uninterpretedFunction().codomain()));
			mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(vars.back(), *uf, false))));
		} else {
			SMTRAT_LOG_ERROR("smtrat.parser", "The function argument type for function " << f << " was invalid.");
			continue;
		}
		mUninterpretedArguments[v] = vars.back();
	}
	return carl::newUFInstance(f, vars);
}
FormulaT ParserState::applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
	carl::Variable v = carl::freshBooleanVariable();
	mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(carl::UVariable(v), applyUninterpretedFunction(f, args), false))));
	return FormulaT(v);
}
Poly ParserState::applyUninterpretedTheoryFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
	assert(carl::SortManager::getInstance().isInterpreted(f.codomain()));

	carl::Variable v = carl::freshVariable(carl::SortManager::getInstance().interpretedType(f.codomain()));
	mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(carl::UVariable(v), applyUninterpretedFunction(f, args), false))));
	return Poly(v);
}

carl::Variable ParserState::addVariableBinding(const std::pair<std::string, carl::Sort>& b) {
	assert(isSymbolFree(b.first));
	switch (TypeOfTerm::get(b.second)) {
	case ExpressionType::BOOLEAN: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, carl::VariableType::VT_BOOL);
		bind_bool.sym.add(b.first, FormulaT(v));
		return v;
	}
	case ExpressionType::THEORY: {
		carl::Variable v = carl::VariablePool::getInstance().getFreshVariable(b.first, carl::SortManager::getInstance().interpretedType(b.second));
		bind_theory.sym.add(b.first, Poly(v));
		return v;
	}
	case ExpressionType::UNINTERPRETED:
		handler->error() << "Tried to bind a uninterpreted variable.";
		return carl::Variable::NO_VARIABLE;
		break;
	default:
		assert(false);
		return carl::Variable::NO_VARIABLE;
	}
}

void ParserState::addTheoryBinding(std::string& _varName, Poly& _polynomial) {
	assert(isSymbolFree(_varName));
	bind_theory.sym.add(_varName, _polynomial);
}

void ParserState::addBooleanBinding(std::string& _varName, const FormulaT& _formula) {
	assert(isSymbolFree(_varName));
	bind_bool.sym.add(_varName, _formula);
}

void ParserState::addUninterpretedBinding(std::string& _varName, const UninterpretedType& _uninterpreted) {
	assert(isSymbolFree(_varName));
	bind_uninterpreted.sym.add(_varName, _uninterpreted);
}

carl::Variable ParserState::addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type) {
	std::string name = _name;
	for (unsigned id = 1; !isSymbolFree(name, false); id++) {
		name = _name + "_q" + std::to_string(id);
	}
	if (type.is_initialized()) {
		switch (TypeOfTerm::get(type.get())) {
			case ExpressionType::BOOLEAN: {
				carl::Variable v = carl::freshBooleanVariable(name);
				var_bool.sym.remove(_name);
				var_bool.sym.add(_name, v);
				return v;
			}
			case ExpressionType::THEORY: {
				carl::Variable v = carl::freshVariable(name, type.get());
				var_theory.sym.remove(_name);
				var_theory.sym.add(_name, v);
				return v;
			}
			default: { // case ExpressionType::UNINTERPRETED
				handler->error() << "Tried to quantify over an uninterpreted type.";
				assert(false);
				return carl::Variable::NO_VARIABLE;
			}
		}
	} else if (var_bool.sym.find(_name) != nullptr) {
		carl::Variable v = carl::freshBooleanVariable(name);
		var_bool.sym.remove(_name);
		var_bool.sym.add(_name, v);
		return v;
	} else if (var_theory.sym.find(_name) != nullptr) {
		carl::Variable v = carl::freshVariable(name, var_theory.sym.at(_name).getType());
		var_theory.sym.remove(_name);
		var_theory.sym.add(_name, v);
		return v;
	} else {
		handler->error() << "Tried to quantify <" << _name << "> but no type could be inferred.";
		return carl::Variable::NO_VARIABLE;
	}
}
}
}
