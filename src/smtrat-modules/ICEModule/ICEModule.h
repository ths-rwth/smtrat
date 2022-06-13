/**
 * @file ICEModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 * 
 * Supports optimization.
 *
 * @version 2015-11-24
 * Created on 2015-11-24.
 */

#pragma once

#include <smtrat-solver/PModule.h>
#include <smtrat-variablebounds/VariableBounds.h>

#include "ICESettings.h"
#include "ForwardHyperGraph.h"

namespace smtrat
{
	template<typename Settings>
	class ICEModule : public PModule
	{
		struct Coefficient {
			Rational r;
			bool strict;
			Coefficient(): r(0), strict(false) {}
			Coefficient(Coefficient&& c): r(c.r), strict(c.strict) {}
			Coefficient(const Coefficient& c): r(c.r), strict(c.strict) {}
			Coefficient& operator=(const Coefficient& c) {
				r = c.r;
				strict = c.strict;
				return *this;
			}
			Coefficient& operator+=(const Coefficient& c) {
				r += c.r;
				strict |= c.strict;
				return *this;
			}
			friend std::ostream& operator<<(std::ostream& os, const Coefficient& c) {
				return os << "(" << c.r << "," << std::boolalpha << c.strict << ")";
			}
		};

		using VertexProperty = TermT;
		struct EdgeProperty {
			Coefficient coeff;
			FormulaT constraint;
			EdgeProperty(const Coefficient& c, const FormulaT& con): coeff(c), constraint(con) {}
			friend std::ostream& operator<<(std::ostream& os, const EdgeProperty& ep) {
				return os << ep.coeff;
			}
		};
		using FHG = ForwardHyperGraph<VertexProperty, EdgeProperty>;
		
		struct CycleCollector {
			using Vertex = typename FHG::Vertex;
			using Edge = typename FHG::Edge;
			
			FormulaSetT mInfeasibleSubset;
			std::vector<std::pair<FormulaT,FormulaT>> mLemmas;
			
			FormulaT buildFormula(const std::vector<Edge>& edges) const {
				FormulasT res;
				std::transform(edges.begin(), edges.end(), std::back_inserter(res), [](const Edge& edge){ return edge->constraint; });
				return FormulaT(carl::FormulaType::AND, std::move(res));
			}
			std::vector<Vertex> collectAdjacent(const std::vector<Vertex>& vertices, const std::vector<Edge>& edges) {
				std::vector<Vertex> res;
				auto curVertex = vertices.begin();
				for (const auto& edge: edges) {
					curVertex++;
					if (curVertex == vertices.end()) curVertex = vertices.begin();
					for (const auto& v: edge.out()) {
						if (v == *curVertex) continue;
						res.push_back(v);
					}
				}
				return res;
			}
			
			/**
			 * Is called whenever a cycle is found.
			 * If true is returned, the search for further cycles is aborted.
			 */
			bool operator()(const FHG& graph, const std::vector<Vertex>& vertices, const std::vector<Edge>& edges) {
				Coefficient sum;
				for (const auto& edge: edges) sum += edge->coeff;
				
				if (carl::is_zero(sum.r)) {
					FormulaT origin = buildFormula(edges);
					if (sum.strict) {
						// Sum is zero but there is a strict inequality -> UNSAT
						mInfeasibleSubset = FormulaSetT(origin.subformulas().begin(), origin.subformulas().end());
						return true;
					} else {
						// Sum is zero and all inequalities are weak
						// -> Variables on the cycle
						for (const auto& v: collectAdjacent(vertices, edges)) {
							FormulaT lemma(Poly(graph[v]), carl::Relation::EQ);
							SMTRAT_LOG_DEBUG("smtrat.ice", "Deducted " << lemma);
							mLemmas.emplace_back(lemma, origin);
						}
						for (std::size_t i = 1; i < vertices.size(); i++) {
							const auto& a = graph[vertices[i-1]];
							const auto& b = graph[vertices[i]];
							FormulaT lemma(a - b + edges[i-1]->coeff.r, carl::Relation::EQ);
							SMTRAT_LOG_DEBUG("smtrat.ice", "Deducted " << lemma);
							mLemmas.emplace_back(lemma, origin);
						}
					}
				} else if (sum.r > 0) {
					SMTRAT_LOG_DEBUG("smtrat.ice", "What to do? sum > 0");
				} else if (sum.r < 0) {
					FormulaT origin = buildFormula(edges);
					mInfeasibleSubset = FormulaSetT(origin.subformulas().begin(), origin.subformulas().end());
					return true;
				}
				return false;
			}
		};

		private:
			vb::VariableBounds<FormulaT> mBounds;
			std::map<FormulaT,ConstraintT> mConstraints;
			std::set<FormulaT> mOtherFormulas;
			
			void addFormula(const FormulaT& f);
			void removeFormula(const FormulaT& f);
			Answer processConstraints();
			
			bool is_zero(const TermT& t) const {
				return mBounds.getInterval(t).is_zero();
			}
			bool isSemiPositive(const TermT& t) const {
				return mBounds.getInterval(t).is_semi_positive();
			}
			bool isSemiNegative(const TermT& t) const {
				return mBounds.getInterval(t).is_semi_negative();
			}
			bool isSuitable(const ConstraintT& c, TermT& src, std::vector<TermT>& dest, Coefficient& coeff);
			
		public:
			typedef Settings SettingsType;
			ICEModule(const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager = nullptr);

			~ICEModule();

			/**
			 * The module has to take the given sub-formula of the received formula into account.
			 *
			 * @param _subformula The sub-formula to take additionally into account.
			 * @return false, if it can be easily decided that this sub-formula causes a conflict with
			 *		  the already considered sub-formulas;
			 *		  true, otherwise.
			 */
			bool addCore( ModuleInput::const_iterator _subformula );

			/**
			 * Removes the subformula of the received formula at the given position to the considered ones of this module.
			 * Note that this includes every stored calculation which depended on this subformula, but should keep the other
			 * stored calculation, if possible, untouched.
			 *
			 * @param _subformula The position of the subformula to remove.
			 */
			void removeCore( ModuleInput::const_iterator _subformula );

			/**
			 * Checks the received formula for consistency.
			 * @return SAT,	if the received formula is satisfiable;
			 *		 UNSAT,   if the received formula is not satisfiable;
			 *		 Unknown, otherwise.
			 */
			Answer checkCore();
	};
}
