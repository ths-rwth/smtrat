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
			Scope(const ParserState& state)
			{
				this->var_bool = state.var_bool.sym;
				this->var_theory = state.var_theory.sym;
				this->var_uninterpreted = state.var_uninterpreted.sym;
				this->bind_bool = state.bind_bool.sym;
				this->bind_theory = state.bind_theory.sym;
				this->bind_uninterpreted = state.bind_uninterpreted.sym;
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
			assert(this != nullptr);
			mScopeStack.emplace(*this);
		}
		void popScope() {
			mScopeStack.top().restore(*this);
			mScopeStack.pop();
		}

		bool checkArguments(const std::string& name, const std::vector<carl::Variable>& types, const Arguments& args, std::map<carl::Variable, FormulaT>& boolAssignments, std::map<carl::Variable, Poly>& theoryAssignments);

		void errorMessage(const std::string& msg) {
			std::cerr << "Parser error: " << msg << std::endl;
		}
		bool isSymbolFree(const std::string& name, bool output = true);
		
		FormulaT applyBooleanFunction(const BooleanFunction& f, const Arguments& args);
		Poly applyTheoryFunction(const TheoryFunction& f, const Arguments& args);
		carl::UFInstance applyUninterpretedFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		FormulaT applyUninterpretedBooleanFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		Poly applyUninterpretedTheoryFunction(const carl::UninterpretedFunction& f, const Arguments& args);
		
		

		carl::Variable addVariableBinding(const std::pair<std::string, carl::Sort>& b);
		void addTheoryBinding(std::string& _varName, Poly&);
		void addBooleanBinding(std::string&, const FormulaT&);
		void addUninterpretedBinding(std::string&, const UninterpretedType&);
		
		carl::Variable addQuantifiedVariable(const std::string& _name, const boost::optional<carl::VariableType>& type);
	};

}
}