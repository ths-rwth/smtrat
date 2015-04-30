/* 
 * @file   ParserState.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"
#include "TheoryTypes.h"
#include "FunctionInstantiator.h"

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
		std::map<std::string, types::TermType> defined_constants;
		std::map<std::string, const FunctionInstantiator*> defined_functions;
		std::map<std::string, const IndexedFunctionInstantiator*> defined_indexed_functions;
	
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
				else if (defined_constants.find(name) != defined_constants.end()) out << "\"" << name << "\" has already been defined as a constant.";
				else if (declared_functions.find(name) != declared_functions.end()) out << "\"" << name << "\" has already been declared as a function.";
				else if (defined_functions.find(name) != defined_functions.end()) out << "\"" << name << "\" has already been defined as a function.";
				else if (defined_indexed_functions.find(name) != defined_indexed_functions.end()) out << "\"" << name << "\" has already been defined as a function.";
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
		
		bool resolveSymbol(const std::string& name, types::TermType& r) const {
			if (resolveSymbol(name, variables, r)) return true;
			if (resolveSymbol(name, bindings, r)) return true;
			if (resolveSymbol(name, defined_constants, r)) return true;
			return false;
		}
		
		void registerFunction(const std::string& name, const FunctionInstantiator* fi) {
			if (!isSymbolFree(name)) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to register function \"" << name << "\", name is already used.");
				return;
			}
			defined_functions.emplace(name, fi);
		}
		void registerFunction(const std::string& name, const IndexedFunctionInstantiator* fi) {
			if (!isSymbolFree(name)) {
				SMTRAT_LOG_ERROR("smtrat.parser", "Failed to register indexed function \"" << name << "\", name is already used.");
				return;
			}
			defined_indexed_functions.emplace(name, fi);
		}
	};

}
}
