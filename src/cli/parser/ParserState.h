/* 
 * @file   ParserState.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "ParserUtils.h"

namespace smtrat {
namespace parser {
	
	struct ParserState {

		struct Scope {
		private:
			qi::symbols<char, carl::Variable> var_bool;
			qi::symbols<char, carl::Variable> var_theory;
			qi::symbols<char, carl::UVariable> var_uninterpreted;
			qi::symbols<char, FormulaT> bind_bool;
			qi::symbols<char, Poly> bind_theory;
			qi::symbols<char, UninterpretedType> bind_uninterpreted;
		public:
			Scope(const ParserState& parser)
			{
				this->var_bool = parser.var_bool.sym;
				this->var_theory = parser.var_theory.sym;
				this->var_uninterpreted = parser.var_uninterpreted.sym;
				this->bind_bool = parser.bind_bool.sym;
				this->bind_theory = parser.bind_theory.sym;
				this->bind_uninterpreted = parser.bind_uninterpreted.sym;
			}
			void restore(ParserState& state) {
				state.var_bool.sym = this->var_bool;
				state.var_theory.sym = this->var_theory;
				state.var_uninterpreted.sym = this->var_uninterpreted;
				state.bind_bool.sym = this->bind_bool;
				state.bind_theory.sym = this->bind_theory;
				state.bind_uninterpreted.sym = this->bind_uninterpreted;
			}
		};

		DeclaredSymbolParser<carl::Variable> var_bool;
		DeclaredSymbolParser<carl::Variable> var_theory;
		DeclaredSymbolParser<carl::UVariable> var_uninterpreted;

		DeclaredSymbolParser<FormulaT> bind_bool;
		DeclaredSymbolParser<Poly> bind_theory;
		DeclaredSymbolParser<UninterpretedType> bind_uninterpreted;
	
		qi::symbols<char, BooleanFunction> funmap_bool;
		qi::symbols<char, TheoryFunction> funmap_theory;
		qi::symbols<char, carl::UninterpretedFunction> funmap_ufbool;
		qi::symbols<char, carl::UninterpretedFunction> funmap_uftheory;
		qi::symbols<char, carl::UninterpretedFunction> funmap_uf;
	
		smtrat::Logic mLogic;
		std::set<FormulaT> mTheoryIteBindings;
		std::set<FormulaT> mUninterpretedEqualities;
		std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mTheoryItes;
		
		InstructionHandler* handler;
		
		std::stack<Scope> mScopeStack;
		
		ParserState(InstructionHandler* ih): handler(ih) {
			var_bool.sym.name("declared boolean variable");
			var_theory.sym.name("declared theory variable");
			bind_bool.sym.name("bound boolean variable");
			bind_theory.sym.name("bound theory variable");
		}
		
		void pushScope() {
			mScopeStack.emplace(*this);
		}
		void popScope() {
			mScopeStack.top().restore(*this);
			mScopeStack.pop();
		}

		bool checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, FormulaT>& boolAssignments, std::map<carl::Variable, Poly>& theoryAssignments) {
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

		void errorMessage(const std::string& msg) {
			std::cerr << "Parser error: " << msg << std::endl;
		}
		bool isSymbolFree(const std::string& name, bool output = true) {
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
		
		carl::UFInstance applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args) {
			std::vector<carl::UVariable> vars;
			for (auto v: args) {
				if (FormulaT* f = boost::get<FormulaT>(&v)) {
					carl::Variable tmp = carl::newAuxiliaryBooleanVariable();
					vars.push_back(carl::UVariable(tmp));
					mUninterpretedEqualities.insert(FormulaT(carl::FormulaType::AND, FormulaT(tmp), *f));
				} else if (Poly* p = boost::get<Poly>(&v)) {
					carl::Variable tmp = carl::newAuxiliaryRealVariable();
					vars.push_back(carl::UVariable(tmp));
					mUninterpretedEqualities.insert(FormulaT(*p - tmp, carl::Relation::EQ));
				} else if (carl::UVariable* uv = boost::get<carl::UVariable>(&v)) {
					vars.push_back(*uv);
				} else if (carl::UFInstance* uf = boost::get<carl::UFInstance>(&v)) {
					carl::Variable tmp = carl::newAuxiliaryUninterpretedVariable();
					vars.push_back(carl::UVariable(tmp, uf->uninterpretedFunction().codomain()));
					mUninterpretedEqualities.insert(FormulaT(std::move(carl::UEquality(vars.back(), *uf, false))));
				}
			}
			return carl::newUFInstance(f, vars);
		}
	};

}
}