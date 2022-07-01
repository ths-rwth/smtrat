#ifndef SRC_LIB_MODULES_EQMODULE_EQMODULEPRINTING_TPP_
#define SRC_LIB_MODULES_EQMODULE_EQMODULEPRINTING_TPP_

#include "EQModule.h"

#include <fstream>
#include <iostream>
#include <boost/lexical_cast.hpp>

namespace smtrat {
	template<typename Settings> template<typename EdgeType>
		void EQModule<Settings>::P_print_edge(std::ostream& out, EdgeType* edge, FormulaSetT& infeasible, std::unordered_set< g_iterator, by_address_hasher<g_iterator> >& inserted_nodes)
	{
		if(edge->mPred->second.mUFIndex < edge->mSucc->second.mUFIndex) {
			
			out << "\"" << edge->mPred->first << "\"";
			out << " -- ";
			out << "\"" << edge->mSucc->first << "\"";
			
			if (std::is_same<EdgeType, ineq_edge_info>::value) {
				out << "[color=violet,penwidth=3.0, label=\"";
				out << " (";
				out << ((ineq_edge_info*) edge)->mRealPred->first;
				out << ",";
				out << ((ineq_edge_info*) edge)->mRealSucc->first;
				out << ") ";
				out << "\"]";
			} else if (std::is_same<EdgeType, implicit_edge_info>::value) {
				out << "[style=dashed,color=green,penwidth=3.0, label=\"";
				out << " (";
				out << ((implicit_edge_info*) edge)->mRealPred->first;
				out << ",";
				out << ((implicit_edge_info*) edge)->mRealSucc->first;
				out << ",";
				out << ((implicit_edge_info*) edge)->mID;
				out << ") ";
				out << "\"]";
			}
			
			if(!mInfeasibleSubsets.empty()) {
				for (const FormulaT& formula : infeasible) {
					if (	(formula.u_equality().lhs() == edge->mPred->first && formula.u_equality().rhs() == edge->mSucc->first)
						||	(formula.u_equality().rhs() == edge->mPred->first && formula.u_equality().lhs() == edge->mSucc->first)) {

						if (!formula.u_equality().negated()) {
							out << "[color=red,penwidth=3.0]";
						}

						break;
					}
				}
			}

			out << ";\n";

			if (inserted_nodes.insert(edge->mPred).second) {

				out << "\"" << edge->mPred->first << "\"[";
				
				if (mUnionFind.find(edge->mPred->second.mUFIndex) == edge->mPred->second.mUFIndex) {
					if (mComponentUnionFind.find(mUnionFind.find(edge->mPred->second.mUFIndex)) == mUnionFind.find(edge->mPred->second.mUFIndex)) {
						out << "shape=\"rect\" fontcolor=green ";
					} else {
						out << "shape=\"rect\" fontcolor=blue ";
					}
				}

				if(!mInfeasibleSubsets.empty()) {
					for (const FormulaT& formula : infeasible) {
						if (formula.u_equality().lhs() == edge->mPred->first || formula.u_equality().rhs() == edge->mPred->first) {
							out << "color=red ";
							break;
						}
					}
				}


				out << "];\n";
			}

			if (inserted_nodes.insert(edge->mSucc).second) {

				out << "\"" << edge->mSucc->first << "\"[";
				
				if (mUnionFind.find(edge->mSucc->second.mUFIndex) == edge->mSucc->second.mUFIndex) {
					if (mComponentUnionFind.find(mUnionFind.find(edge->mSucc->second.mUFIndex)) == mUnionFind.find(edge->mSucc->second.mUFIndex)) {
						out << "shape=\"rect\" fontcolor=green ";
					} else {
						out << "shape=\"rect\" fontcolor=blue ";
					}
				}

				if(!mInfeasibleSubsets.empty()) {
					for (const FormulaT& formula : infeasible) {
						if (formula.u_equality().lhs() == edge->mSucc->first || formula.u_equality().rhs() == edge->mSucc->first) {
							out << "color=red ";
							break;
						}
					}
				}

				out << "];\n";
			}
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_print_graph()
	{
		std::unordered_set< g_iterator, by_address_hasher<g_iterator> > inserted_nodes;

		static int visualiseGraphCount = 0;
		std::ofstream file;

		FormulaSetT& infeasible = mInfeasibleSubsets.back();
		
		std::string fileName("graphs/graph" + boost::lexical_cast<std::string>(visualiseGraphCount++) + ".dot");
		file.open(fileName.c_str(), std::fstream::out | std::fstream::trunc);

		if(file) {
			std::cout << "Printing graph to '" << fileName << '\'' << std::endl;
			file << "graph {\n";
			if(!mInfeasibleSubsets.empty()) {
				for (const FormulaT& formula : infeasible) {
					if (formula.u_equality().negated()) {
						file << "labelloc=\"t\";\n";
						file << "label = \"" << formula << "\";\n";

						g_iterator itrLhs = mEqualityGraph.find(formula.u_equality().lhs());
						g_iterator itrRhs = mEqualityGraph.find(formula.u_equality().rhs());

						if (inserted_nodes.insert(itrLhs).second) {
							file << "\"" << formula.u_equality().lhs() << "\"[fillcolor=yellow, style=\"filled\" ";
							

							if (mUnionFind.find(itrLhs->second.mUFIndex) == itrLhs->second.mUFIndex) {
								if (mComponentUnionFind.find(mUnionFind.find(itrLhs->second.mUFIndex)) == mUnionFind.find(itrLhs->second.mUFIndex)) {
									file << "shape=\"rect\" fontcolor=green ";
								} else {
									file << "shape=\"rect\" fontcolor=blue ";
								}
							}
							file << "];\n";
						}

						if (inserted_nodes.insert(itrRhs).second) {
							file << "\"" << formula.u_equality().rhs() << "\"[fillcolor=yellow, style=\"filled\" ";

							if (mUnionFind.find(itrRhs->second.mUFIndex) == itrRhs->second.mUFIndex) {
								if (mComponentUnionFind.find(mUnionFind.find(itrRhs->second.mUFIndex)) == mUnionFind.find(itrRhs->second.mUFIndex)) {
									file << "shape=\"rect\" fontcolor=green ";
								} else  {
									file << "shape=\"rect\" fontcolor=blue";
								}
							}
							file << "];\n";
						}
					}
				}
			}

			for (g_iterator itr = mEqualityGraph.begin(); itr != mEqualityGraph.end(); ++itr) {
				for(edge_info* edge : itr->second.mExplicit) {
					P_print_edge(file, edge, infeasible, inserted_nodes);
				}

				for(implicit_edge_info* edge : itr->second.mImplicit) {
					P_print_edge(file, edge, infeasible, inserted_nodes);
				}
			}
			
			for(ineq_edge_info* edge : mPossibleInconsistencies) {
				P_print_edge(file, edge, infeasible, inserted_nodes);
			}

			file << "}" << std::endl;
			file.close();
		}
	}

	template<typename Settings>
		void EQModule<Settings>::P_print_infeasible_subset()
	{
		static unsigned formulaCount = 0;

		for(const FormulaSetT &infeasible : mInfeasibleSubsets) {
			std::ofstream file("formulas/infeasible_subset_" + boost::lexical_cast<std::string>(++formulaCount)+".smt2");

			if(file) {
				file << "(set-logic QF_UF)" << std::endl;
				file << "(set-info :status unsat)" << std::endl;

				std::unordered_set<Sort> sorts;
				std::unordered_set<UninterpretedFunction> functions;
				std::unordered_set<UVariable> variables;

				for(const FormulaT &formula : infeasible) {
					const UEquality &ueq = formula.u_equality();

					if(ueq.lhs().isUFInstance()) {
						functions.insert(ueq.lhs().asUFInstance().uninterpretedFunction());
						sorts.insert(ueq.lhs().asUFInstance().uninterpretedFunction().codomain());
						for(const Sort& s : ueq.lhs().asUFInstance().uninterpretedFunction().domain()) {
							sorts.insert(s);
						}
						for(const auto& t : ueq.lhs().asUFInstance().args()) {
							assert(t.isUVariable());
							const auto& v = t.asUVariable();
							variables.insert(v);
						}
					} else {
						variables.insert(ueq.lhs().asUVariable());
						sorts.insert(ueq.lhs().asUVariable().domain());
					}

					if(ueq.rhs().isUFInstance()) {
						functions.insert(ueq.rhs().asUFInstance().uninterpretedFunction());
						sorts.insert(ueq.rhs().asUFInstance().uninterpretedFunction().codomain());
						for(const Sort& s : ueq.rhs().asUFInstance().uninterpretedFunction().domain()) {
							sorts.insert(s);
						}
						for(const auto& t : ueq.rhs().asUFInstance().args()) {
							assert(t.isUVariable());
							const auto& v = t.asUVariable();
							variables.insert(v);
						}
					} else {
						variables.insert(ueq.rhs().asUVariable());
						sorts.insert(ueq.rhs().asUVariable().domain());
					}
				}

				for(const Sort& s : sorts) {
					file << "(declare-sort " << s << " 0)" << std::endl;
				}

				for(const UninterpretedFunction& fun : functions) {
					file << "(declare-fun " << fun.name() << " (";
					for(const Sort& s : fun.domain()) {
						file << s << " ";
					}
					file << ") " << fun.codomain() << ")" << std::endl;
				}

				for(const UVariable& var : variables) {
					file << "(declare-fun " << var << " () " << var.domain() << ")" << std::endl;
				}

				for(const FormulaT& formula : infeasible) {
					file << "(assert ";
					if(formula.u_equality().negated()) {
						file << "(not ";
					}

					file << "(= " << formula.u_equality().lhs() << " " << formula.u_equality().rhs() << ")";

					if(formula.u_equality().negated()) {
						file << ")";
					}

					file << ")" << std::endl;
				}

				file << "(check-sat)" << std::endl;
			}
		}
	}



	template<typename Settings>
		void EQModule<Settings>::P_print_bucket_sets()
	{
		if(!mFunctionMap.empty()) {
			std::unordered_set<hash_bucket_type*> foundBuckets;

			for(auto&& entry : mFunctionMap) {
				std::cout << "------------ " << entry.first.name() << " ------------" << std::endl;
				entry.second.mHashBuckets.P_print_buckets(foundBuckets);
			}

			for(std::size_t i = 0; i < mComponentUnionFind.size(); ++i) {
				for(bucket_list_entry &e : mComponentUnionFind[i].mBuckets) {
					if(!foundBuckets.count(e.mBucket)) {
						std::cout << "Found inconsistency in argument bucket list for class " << i << std::endl;
						std::cout << "\t" << "Bucket with hash " << e.mBucket->hashValue << " and classes ";
						for(std::size_t i = 0; i < e.mBucketSet->mArity; ++i) {
							std::cout << e.mBucket->classes[i].mClass << " ";
						}
						std::cout << std::endl;

						for(hash_bucket_entry& ecur : e.mBucket->mEntries) {
							std::cout << "\t\t" << ecur.value->first << std::endl;
						}
					}
				}
			}

			std::cout << "----------------------------" << std::endl;
		}
	}

	template<typename Settings>
		void EQModule<Settings>::hash_bucket_set::P_print_buckets(std::unordered_set<bucket*>& foundBuckets)
	{
		const std::size_t binCount = 1 << mBinShift;

		for(std::size_t i = 0; i < binCount; ++i) {
			bin& bin_ = mBinPtr[i];

			if(!bin_.empty()) {
				std::cout << "Bin "  << i << std::endl;

				for(bucket &cur : bin_) {
					foundBuckets.insert(&cur);

					std::cout << "\t" << "Bucket with hash " << cur.hashValue << " and classes ";
					for(std::size_t i = 0; i < mArity; ++i) {
						std::size_t c = cur.classes[i].mClass;
						std::size_t rc = mModule.mComponentUnionFind.find(mModule.mUnionFind.find(mModule.argsof(cur.mEntries.front()->value)[i]->second.mUFIndex));

						if(c == rc) {
							std::cout << c << " ";
						} else {
							std::cout << c << "(" << rc << ") ";
						}
					}
					std::cout << std::endl;

					for(entry& ecur : cur.mEntries) {
						std::cout << "\t\t" << ecur.value->first << std::endl;
					}

					if(!cur.supportedEdges.empty()) {
						std::cout << "\t\tSupported edges:" << std::endl;
						for(implicit_edge_info* edge : cur.supportedEdges) {
							std::cout << "\t\t\t";
							std::cout << "('" << edge->mPred->first << "', '" << edge->mSucc->first << "'), real: ('" << edge->mRealPred->first << "', '" << edge->mRealSucc->first << "')" << std::endl;
						}
					}
				}
			}
		}
	}
}

#endif
