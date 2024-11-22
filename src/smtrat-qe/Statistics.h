#pragma once

#include <carl-arith/core/Variable.h>
#include <chrono>
#include <smtrat-common/smtrat-common.h>
#include <smtrat-mcsat/variableordering/VariableOrdering.h>
#include <smtrat-coveringng/types.h>

#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>

namespace smtrat {

class QeStatistics : public Statistics {
private:
	size_t output_amount_atoms = 0 ;
	size_t output_amount_or = 0 ;
	size_t output_amount_and = 0 ;
	size_t output_max_var_degree = 0 ;
	size_t output_amount_ire = 0 ;
	size_t output_amount_atoms_eq = 0 ;
	size_t tree_num_nodes = 0;
	size_t tree_num_leaves = 0;
	size_t tree_num_leaves_true = 0;
	size_t tree_num_leaves_false = 0;
	size_t tree_simplified_num_nodes = 0;
	size_t tree_simplified_num_leaves = 0;
	size_t tree_simplified_num_leaves_true = 0;
	size_t tree_simplified_num_leaves_false = 0;

public:
	void collect() override {
		Statistics::addKeyValuePair("output_amount_atoms", output_amount_atoms);
		Statistics::addKeyValuePair("output_amount_or", output_amount_or);
		Statistics::addKeyValuePair("output_amount_and", output_amount_and);
		Statistics::addKeyValuePair("output_max_var_degree", output_max_var_degree);
		Statistics::addKeyValuePair("output_amount_ire", output_amount_ire);
		Statistics::addKeyValuePair("output_amount_atoms_eq", output_amount_atoms_eq);
		Statistics::addKeyValuePair("tree_num_nodes", tree_num_nodes);
		Statistics::addKeyValuePair("tree_num_leaves", tree_num_leaves);
		Statistics::addKeyValuePair("tree_num_leaves_true", tree_num_leaves_true);
		Statistics::addKeyValuePair("tree_num_leaves_false", tree_num_leaves_false);
		Statistics::addKeyValuePair("tree_simplified_num_nodes", tree_simplified_num_nodes);
		Statistics::addKeyValuePair("tree_simplified_num_leaves", tree_simplified_num_leaves);
		Statistics::addKeyValuePair("tree_simplified_num_leaves_true", tree_simplified_num_leaves_true);
		Statistics::addKeyValuePair("tree_simplified_num_leaves_false", tree_simplified_num_leaves_false);
	}

	void process_tree(const smtrat::covering_ng::ParameterTree& tree) {
		if (tree.variable) {
			tree_num_nodes++;
			if (tree.status == 0) {
				tree_num_leaves++;
				tree_num_leaves_true++;
			} else if (tree.status == 1) {
				tree_num_leaves++;
				tree_num_leaves_false++;
			}
		}
		for (const auto& sub : tree.children) {
			process_tree(sub);
		}
	}

	void process_simplified_tree(const smtrat::covering_ng::ParameterTree& tree) {
		if (tree.variable) {
			tree_simplified_num_nodes++;
			if (tree.status == 0) {
				tree_simplified_num_leaves++;
				tree_simplified_num_leaves_true++;
			} else if (tree.status == 1) {
				tree_simplified_num_leaves++;
				tree_simplified_num_leaves_false++;
			}
		}
		for (const auto& sub : tree.children) {
			process_simplified_tree(sub);
		}
	}

	void process_output_formula(const FormulaT& output_formula) {
		carl::visit(output_formula, [&](const FormulaT& f){
			if(f.is_atom() && f.type() != carl::FormulaType::FALSE && f.type() != carl::FormulaType::TRUE){
				++output_amount_atoms;
				if(f.type() == carl::FormulaType::VARCOMPARE && std::holds_alternative<typename VariableComparisonT::MR>(f.variable_comparison().value())){
					output_amount_ire++;
					output_max_var_degree = std::max(output_max_var_degree, std::get<typename VariableComparisonT::MR>(f.variable_comparison().value()).poly().total_degree());

					if (f.variable_comparison().relation() == carl::Relation::EQ || f.variable_comparison().relation() == carl::Relation::NEQ) {
						output_amount_atoms_eq++;
					}
				}else if(f.type() == carl::FormulaType::CONSTRAINT){
					output_max_var_degree = std::max(output_max_var_degree, f.constraint().lhs().total_degree());

					if (f.constraint().relation() == carl::Relation::EQ || f.constraint().relation() == carl::Relation::NEQ) {
						output_amount_atoms_eq++;
					}
				}
			}else if(f.type() == carl::FormulaType::OR) {
				output_amount_or += f.subformulas().size() - 1;
			}else if(f.type() == carl::FormulaType::AND) {
				output_amount_and += f.subformulas().size() - 1;
			}
		});
	}

	static QeStatistics& get_instance() {
		static QeStatistics& statistics = statistics_get<QeStatistics>("qe");
		return statistics;
	}
};

} // namespace smtrat

#endif