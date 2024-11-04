#pragma once

#include <carl-arith/core/Variable.h>
#include <chrono>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>

#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {

class QeNucadStatistics : public Statistics {
private:
	size_t parameter_true_cell = 0;
	size_t parameter_false_cell = 0 ;
	size_t output_amount_atoms = 0 ;
	size_t output_amount_or = 0 ;
	size_t output_amount_and = 0 ;
	size_t output_max_var_degree = 0 ;
	size_t output_amount_ire = 0 ;
	std::string mVariableOrderingHeuristic;
	std::vector<carl::Variable> mVariableOrdering;

public:
	void collect() override {
		Statistics::addKeyValuePair("parameter_amount_true_cells", parameter_true_cell);
		Statistics::addKeyValuePair("parameter_amount_false_cells", parameter_false_cell);
		Statistics::addKeyValuePair("output_amount_atoms", output_amount_atoms);
		Statistics::addKeyValuePair("output_amount_or", output_amount_or);
		Statistics::addKeyValuePair("output_amount_and", output_amount_and);
		Statistics::addKeyValuePair("output_max_var_degree", output_max_var_degree);
		Statistics::addKeyValuePair("output_amount_ire", output_amount_ire);

	}

	void true_cell() {
		++parameter_true_cell;
	}
	void false_cell() {
		++parameter_false_cell;
	}

	void process_output_formula(const FormulaT& output_formula) {
		carl::visit(output_formula, [&](const FormulaT& f){
			if(f.is_atom() && f.type() != carl::FormulaType::FALSE && f.type() != carl::FormulaType::TRUE){
				++output_amount_atoms;
				if(f.type() == carl::FormulaType::VARCOMPARE && std::holds_alternative<typename VariableComparisonT::MR>(f.variable_comparison().value())){
					output_amount_ire++;
					output_max_var_degree = std::max(output_max_var_degree, std::get<typename VariableComparisonT::MR>(f.variable_comparison().value()).poly().total_degree());

				}else if(f.type() == carl::FormulaType::CONSTRAINT){
					output_max_var_degree = std::max(output_max_var_degree, f.constraint().lhs().total_degree());
				}
			}else if(f.type() == carl::FormulaType::OR) {
				output_amount_or += f.subformulas().size() - 1;
			}else if(f.type() == carl::FormulaType::AND) {
				output_amount_and += f.subformulas().size() - 1;
			}
		});
	}

	static QeNucadStatistics& get_instance() {
		static QeNucadStatistics& statistics = statistics_get<QeNucadStatistics>("qe_nucad");
		return statistics;
	}
};

} // namespace smtrat

#endif