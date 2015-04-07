/* 
 * @file   ParserState.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include "../Common.h"

namespace smtrat {
namespace parser {
	
	struct InstructionHandler;
	
	struct ParserState {

		struct Scope {
		private:
			std::map<std::string, carl::Variable> var_bool;
			std::map<std::string, carl::Variable> var_arithmetic;
			std::map<std::string, carl::UVariable> var_uninterpreted;
			std::map<std::string, FormulaT> bind_bool;
			std::map<std::string, Poly> bind_arithmetic;
			//std::map<std::string, UninterpretedType> bind_uninterpreted;
		public:
			Scope(const ParserState& state)
			{
				this->var_bool = state.var_bool;
				this->var_arithmetic = state.var_arithmetic;
				this->var_uninterpreted = state.var_uninterpreted;
				this->bind_bool = state.bind_bool;
				this->bind_arithmetic = state.bind_arithmetic;
				//this->bind_uninterpreted = state.bind_uninterpreted;
			}
			void restore(ParserState& state) {
				state.var_bool = this->var_bool;
				state.var_arithmetic = this->var_arithmetic;
				state.var_uninterpreted = this->var_uninterpreted;
				state.bind_bool = this->bind_bool;
				state.bind_arithmetic = this->bind_arithmetic;
				//state.bind_uninterpreted = this->bind_uninterpreted;
			}
		};

		std::map<std::string, carl::Variable> var_bool;
		std::map<std::string, carl::Variable> var_arithmetic;
		std::map<std::string, carl::UVariable> var_uninterpreted;
		std::map<std::string, FormulaT> bind_bool;
		std::map<std::string, Poly> bind_arithmetic;
		//std::map<std::string, UninterpretedType> bind_uninterpreted;
	
		//std::map<std::string, BooleanFunction> funmap_bool;
		//std::map<std::string, ArithmeticFunction> funmap_arithmetic;
		//std::map<std::string, carl::UninterpretedFunction> funmap_ufbool;
		//std::map<std::string, carl::UninterpretedFunction> funmap_ufarithmetic;
		//std::map<std::string, carl::UninterpretedFunction> funmap_uf;

		FormulasT mArithmeticIteBindings;
		FormulasT mUninterpretedEqualities;
		//std::map<Argument, carl::UVariable> mUninterpretedArguments;
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
				if (name == "true" || name == "false") out << "'" << name << "' is a reserved keyword.";
				else if (this->var_bool.find(name) != var_bool.end()) out << "'" << name << "' has already been defined as a boolean variable.";
				else if (this->var_arithmetic.find(name) != var_arithmetic.end()) out << "'" << name << "' has already been defined as a theory variable.";
				//else if (this->var_uninterpreted.find(name) != var_uninterpreted.end()) out << "'" << name << "' has already been defined as an uninterpreted variable.";
				else if (this->bind_bool.find(name) != bind_bool.end()) out << "'" << name << "' has already been defined as a boolean binding.";
				else if (this->bind_arithmetic.find(name) != bind_arithmetic.end()) out << "'" << name << "' has already been defined as a theory binding.";
				//else if (this->bind_uninterpreted.find(name) != bind_uninterpreted.end()) out << "'" << name << "' has already been defined as an uninterpreted binding.";
				//else if (this->funmap_bool.find(name) != funmap_bool.end()) out << "'" << name << "' has already been defined as a boolean function.";
				//else if (this->funmap_theory.find(name) != funmap_theory.end()) out << "'" << name << "' has already been defined as a theory funtion.";
				//else if (this->funmap_ufbool.find(name) != funmap_ufbool.end()) out << "'" << name << "' has already been defined as an uninterpreted function of boolean return type.";
				//else if (this->funmap_uftheory.find(name) != funmap_uftheory.end()) out << "'" << name << "' has already been defined as an uninterpreted function of theory return type.";
				//else if (this->funmap_uf.find(name) != funmap_uf.end()) out << "'" << name << "' has already been defined as an uninterpreted function.";
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
			if (resolveSymbol(name, var_bool, r)) return r;
			if (resolveSymbol(name, var_arithmetic, r)) return r;
			if (resolveSymbol(name, bind_bool, r)) return r;
			if (resolveSymbol(name, bind_arithmetic, r)) return r;
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
