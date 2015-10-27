/**
 * @file LICModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-03
 * Created on 2015-09-03.
 */

#pragma once

#include "../../solver/PModule.h"
#include "../../datastructures/VariableBounds.h"
#include "LICStatistics.h"
#include "LICSettings.h"

#include <boost/graph/strong_components.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/graph_utility.hpp>

namespace smtrat
{
    template<typename Settings>
    class LICModule : public PModule
    {
            struct Coefficient {
                Rational r;
                bool strict;
                Coefficient(): r(0), strict(false) {}
                // Warning: without the move construct, *very* weird errors appear within boost::graph
                // Do *not* implement the matching copy constructor.
                Coefficient(Coefficient&& c): r(c.r), strict(c.strict) {}
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
            struct VertexProperty {
                carl::Variable var;
                Coefficient coeff;
                std::size_t component;
                FormulaT constraint;
                VertexProperty(): var(carl::Variable::NO_VARIABLE), coeff(), component(0), constraint() {}
                friend std::ostream& operator<<(std::ostream& os, const VertexProperty& vp) {
                    if (vp.var == carl::Variable::NO_VARIABLE) {
                        return os << vp.coeff;
                    } else {
                        return os << vp.var;
                    }
                }
            };
            
            typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS, VertexProperty> Graph;
            typedef typename boost::graph_traits<Graph>::out_edge_iterator EdgeIterator;
            typedef typename Graph::vertex_descriptor Vertex;
            
            typedef std::map<carl::Variable, Vertex> VertexMap;
            
            struct VertexPropertyWriter {
            private:
                const Graph& g;
                std::vector<std::string> colors = {
                    "aquamarine", "blue", "brown", "coral",
                    "chartreuse", "darkorange", "deepskyblue", "goldenrod",
                    "gray", "magenta", "navy", "olivedrab",
                    "purple", "red", "tomato", "yellow"
                };
            public:
                VertexPropertyWriter(const Graph& graph): g(graph) {}
                void operator()(std::ostream& out, const Vertex& vd) const {
                    out << " [label=\"" << g[vd] << "\", color=\"" << colors[g[vd].component % colors.size()] << "\"]";
                }
            };
            
        private:
            vb::VariableBounds<FormulaT> mBounds;
            std::set<ConstraintT> mConstraints;
            std::set<FormulaT> mOtherFormulas;
            
            std::map<carl::Variable, Rational> mAssignments;
            
            void addFormula(const FormulaT& f);
            void removeFormula(const FormulaT& f);
            
            Answer processConstraints();
            
            bool isSemiPositive(carl::Variable::Arg v) const {
                return mBounds.getInterval(v).isSemiPositive();
            }
            bool isSemiNegative(carl::Variable::Arg v) const {
                return mBounds.getInterval(v).isSemiNegative();
            }
            bool isSuitable(const ConstraintT& c, carl::Variable& src, std::vector<carl::Variable>& dest, Coefficient& coeff);
            
            typename VertexMap::mapped_type getVertex(Graph& g, VertexMap& vm, carl::Variable::Arg v) const;
            Vertex getVertex(Graph& g, const Coefficient& c, const ConstraintT& constraint) const;
            
            Vertex nextInComponent(const Graph& g, const Vertex& source, std::size_t component, std::vector<Vertex>* otherVertices = nullptr) const;
            Answer analyzeCycle(const Graph& g, const Vertex& root);
            
        public:
			typedef Settings SettingsType;
std::string moduleName() const {
return SettingsType::moduleName;
}
            LICModule( const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~LICModule();

            // Main interfaces.

            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *          true, otherwise.
             */
            bool informCore( const FormulaT& _constraint );

            /**
             * Informs all backends about the so far encountered constraints, which have not yet been communicated.
             * This method must not and will not be called more than once and only before the first runBackends call.
             */
	        void init();

            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
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
             * Updates the current assignment into the model.
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
             */
            void updateModel() const;

            /**
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );

    };
}

#include "LICModule.tpp"

#include "LICModuleInstantiation.h"
