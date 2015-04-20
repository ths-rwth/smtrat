/* 
 * @file   ParserState.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"
#include "TheoryTypes.h"

namespace smtrat {
namespace parser {
	
	struct InstructionHandler;
	
	struct ParserState {

		struct Scope {
		private:
			std::map<std::string, types::VariableType> variables;
			std::map<std::string, types::TermType> bindings;
			std::map<std::string, carl::UninterpretedFunction> declared_functions;
		public:
			Scope(const ParserState& state)
			{
				this->variables = state.variables;
				this->bindings = state.bindings;
				this->declared_functions = state.declared_functions;
			}
			void restore(ParserState& state) {
				state.variables = this->variables;
				state.bindings = this->bindings;
				state.declared_functions = this->declared_functions;
			}
		};
		
		std::map<std::string, types::VariableType> variables;
		std::map<std::string, types::TermType> bindings;
		std::map<std::string, carl::UninterpretedFunction> declared_functions;
		std::map<std::string, types::FunctionInstantiator> defined_functions;
	
		//std::map<std::string, BooleanFunction> funmap_bool;
		//std::map<std::string, ArithmeticFunction> funmap_arithmetic;
		//std::map<std::string, carl::UninterpretedFunction> funmap_ufbool;
		//std::map<std::string, carl::UninterpretedFunction> funmap_ufarithmetic;

		FormulasT mArithmeticIteBindings;
		FormulasT mUninterpretedEqualities;
		std::map<types::TermType, carl::UVariable> mUninterpretedArguments;
		std::map<carl::Variable, std::tuple<FormulaT, Poly, Poly>> mArithmeticItes;
		FormulasT mGlobalFormulas;
		
		InstructionHandler* handler;
		
		std::stack<Scope> mScopeStack;
		
		ParserState(InstructionHandler* ih): handler(ih) {
		}
		
		void pushScope() {
			mScopeStack.emplace(*this);
		}
		void popScope() {
			mScopeStack.top().restore(*this);
			mScopeStack.pop();
		}

		//bool checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, FormulaT>& boolAssignments, std::map<carl::Variable, Poly>& theoryAssignments);

		void errorMessage(const std::string& msg) {
			std::cerr << "Parser error: " << msg << std::endl;
		}
		bool isSymbolFree(const std::string& name, bool output = true) {
				std::stringstream out;
				if (name == "true" || name == "false") out << "\"" << name << "\" is a reserved keyword.";
				else if (variables.find(name) != variables.end()) out << "\"" << name << "\" has already been defined as a variable.";
				else if (bindings.find(name) != bindings.end()) out << "\"" << name << "\" has already been defined as a binding to \"" << bindings[name] << "\".";
				else if (declared_functions.find(name) != declared_functions.end()) out << "\"" << name << "\" has already been declared as a function.";
				//else if (funmap_theory.find(name) != funmap_theory.end()) out << "\"" << name << "\" has already been defined as a theory funtion.";
				//else if (funmap_ufbool.find(name) != funmap_ufbool.end()) out << "\"" << name << "\" has already been defined as an uninterpreted function of boolean return type.";
				//else if (funmap_uftheory.find(name) != funmap_uftheory.end()) out << "\"" << name << "\" has already been defined as an uninterpreted function of theory return type.";
				//else if (funmap_uf.find(name) != funmap_uf.end()) out << "\"" << name << "\" has already been defined as an uninterpreted function.";
				else return true;
				if (output) SMTRAT_LOG_ERROR("smtrat.parser", out.str());
				return false;
		}
		
		template<typename Res, typename T>
		bool resolveSymbol(const std::string& name, const std::map<std::string, T>& map, Res& result) const {
			auto it = map.find(name);
			if (it == map.end()) return false;
			result = it->second;
			return true;
		}
		
		template<typename Res>
		Res resolveSymbol(const std::string& name) const {
			Res r;
			if (resolveSymbol(name, variables, r)) return r;
			if (resolveSymbol(name, bindings, r)) return r;
			SMTRAT_LOG_ERROR("smtrat.parser", "Tried to resolve symbol \"" << name << "\" which was not registered.");
			return r;
		}
		
		//FormulaT applyBooleanFunction(const BooleanFunction& f, const Arguments& args);
		//Poly applyTheoryFunction(const TheoryFunction& f, const Arguments& args);
		//carl::UFInstance applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		//FormulaT applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		//Poly applyUninterpretedTheoryFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		
		

		//carl::Variable addVariableBinding(const std::pair<std::string, carl::Sort>& b);
		//void addTheoryBinding(std::string& _varName, Poly&);
		//void addBooleanBinding(std::string&, const FormulaT&);
		//void addUninterpretedBinding(std::string&, const UninterpretedType&);
		
		//carl::Variable addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type);

		/*void printSizeStats() const {
			std::cout << "Vars: " << var_bool.size() << " / " << var_arithmetic.size() << " / " << var_uninterpreted.size() << std::endl;
			std::cout << "Bind: " << bind_bool.size() << " / " << bind_arithmetic.size() << " / " << bind_uninterpreted.size() << std::endl;
		}*/
	};

}
}
