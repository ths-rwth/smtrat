/**
 * @file LICModule.tpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-03
 * Created on 2015-09-03.
 */

#include "LICModule.h"

namespace smtrat
{
	/**
	 * Constructors.
	 */

	template<class Settings>
	LICModule<Settings>::LICModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
		PModule( _formula, _conditionals, _manager ) 
	{}

	/**
	 * Destructor.
	 */

	template<class Settings>
	LICModule<Settings>::~LICModule()
	{}


	template<class Settings>
	bool LICModule<Settings>::informCore( const FormulaT& )
	{
		return true;
	}

	template<class Settings>
	void LICModule<Settings>::init()
	{}

	template<class Settings>
	bool LICModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		addReceivedSubformulaToPassedFormula(_subformula);
		addFormula(_subformula->formula());
		return true;
	}

	template<class Settings>
	void LICModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		removeFormula(_subformula->formula());
	}

	template<class Settings>
	void LICModule<Settings>::updateModel() const
	{
		mModel.clear();
		if (solverState() == True) {
			getBackendsModel();
		}
	}

	template<class Settings>
	Answer LICModule<Settings>::checkCore( bool _full )
	{
		Answer res = processConstraints();
		if (res == False) return False;
		
		res = runBackends(_full);
		if (res == False) getInfeasibleSubsets();
		return res;
	}
	
	template<class Settings>
	void LICModule<Settings>::addFormula(const FormulaT& f) {
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.insert(f.constraint());
				mBounds.addBound(f.constraint(), f);
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), invertRelation(c.relation()));
					mConstraints.insert(newC);
					mBounds.addBound(newC, f);
				}
				break;
			}
			default:
				break;
		}
	}
	
	template<class Settings>
	void LICModule<Settings>::removeFormula(const FormulaT& f) {
		switch (f.getType()) {
			case carl::FormulaType::CONSTRAINT:
				mConstraints.erase(f.constraint());
				mBounds.removeBound(f.constraint(), f);
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), invertRelation(c.relation()));
					mConstraints.erase(newC);
					mBounds.removeBound(newC, f);
				}
				break;
			}
			default:
				break;
		}
	}
	
	template<class Settings>
	Answer LICModule<Settings>::processConstraints() {
		Graph graph;
		VertexMap vertices;
		
		carl::Variable src;
		std::vector<carl::Variable> dest;
		Coefficient coeff;
		for (const auto& c: mConstraints) {
			if (isSuitable(c, src, dest, coeff)) {
				auto srcVertex = getVertex(graph, vertices, src);
				auto edgeVertex = getVertex(graph, coeff, c);
				boost::add_edge(srcVertex, edgeVertex, graph);
				for (const auto& d: dest) {
					auto destVertex = getVertex(graph, vertices, d);
					boost::add_edge(edgeVertex, destVertex, graph);
				}
			}
		}
		
		
		std::vector<std::size_t> component(boost::num_vertices(graph)), discover_time(num_vertices(graph));
		std::vector<boost::default_color_type> color(boost::num_vertices(graph));
		std::vector<Vertex> root(boost::num_vertices(graph));
		std::size_t num = boost::strong_components(graph, boost::make_iterator_property_map(component.begin(), boost::get(boost::vertex_index, graph)), 
							  root_map(boost::make_iterator_property_map(root.begin(), boost::get(boost::vertex_index, graph))).
							  color_map(boost::make_iterator_property_map(color.begin(), boost::get(boost::vertex_index, graph))).
							  discover_time_map(boost::make_iterator_property_map(discover_time.begin(), boost::get(boost::vertex_index, graph))));
		std::vector<std::pair<Vertex,std::size_t>> classes;
		classes.resize(num);
		for (std::size_t i = 0; i < component.size(); i++) {
			graph[i].component = component[i];
			if (classes[component[i]].first == 0) {
				classes[component[i]].first = root[i];
			}
			classes[component[i]].second++;
		}
		assert(classes.size() == num);
		
		if (Settings::dumpAsDot) {
			VertexPropertyWriter vpw(graph);
			std::ofstream out(Settings::dotFilename);
			boost::write_graphviz(out, graph, vpw);
			out.close();
		}
		
		for (const auto& c: classes) {
			if (c.second == 1) continue;
			Answer a = analyzeCycle(graph, c.first);
			if (a == False) return False;
		}
		return True;
	}
	
	template<class Settings>
	bool LICModule<Settings>::isSuitable(const ConstraintT& c, carl::Variable& src, std::vector<carl::Variable>& dest, Coefficient& coeff) {
		SMTRAT_LOG_FUNC("smtrat.lic", c);
		bool invert = false;
		src = carl::Variable::NO_VARIABLE;
		dest.clear();
		coeff.strict = false;

		switch (c.relation()) {
			case carl::Relation::EQ: break;
			case carl::Relation::NEQ: return false;
			case carl::Relation::LESS:
				invert = true;
				coeff.strict = true;
				break;
			case carl::Relation::LEQ:
				invert = true;
				break;
			case carl::Relation::GREATER:
				coeff.strict = true;
				break;
			case carl::Relation::GEQ: break;
		}
		Rational pone = carl::constant_one<Rational>().get();
		Rational mone = -carl::constant_one<Rational>().get();
		Poly p = c.lhs();
		if (invert) p = -p;

		for (const auto& term: p) {
			if (term.isConstant()) continue;
			if (term.coeff() == pone) {
				if (!term.isSingleVariable()) return false;
				carl::Variable v = term.getSingleVariable();
				if (isSemiPositive(v)) {
					if (src != carl::Variable::NO_VARIABLE) return false;
					src = v;
				} else if (isSemiNegative(v)) dest.push_back(v);
				else return false;
			} else if (term.coeff() == mone) {
				if (!term.isSingleVariable()) return false;
				carl::Variable v = term.getSingleVariable();
				if (isSemiPositive(v)) dest.push_back(v);
				else if (isSemiNegative(v)) {
					if (src != carl::Variable::NO_VARIABLE) return false;
					src = v;
				} else return false;
			} else {
				return false;
			}
		}
		if (dest.empty()) return false;
		coeff.r = p.constantPart();
		return true;
	}
	
	template<class Settings>
	typename LICModule<Settings>::VertexMap::mapped_type LICModule<Settings>::getVertex(Graph& g, VertexMap& vm, carl::Variable::Arg v) const {
		auto it = vm.find(v);
		if (it != vm.end()) return it->second;
		auto res = boost::add_vertex(g);
		g[res].var = v;
		vm.emplace(v, res);
		return res;
	}
	template<class Settings>
	typename LICModule<Settings>::Vertex LICModule<Settings>::getVertex(Graph& g, const Coefficient& c, const ConstraintT& constraint) const {
		auto res = boost::add_vertex(g);
		g[res].coeff = c;
		g[res].constraint = FormulaT(constraint);
		return res;
	}
	
	template<class Settings>
	typename LICModule<Settings>::Vertex LICModule<Settings>::nextInComponent(const Graph& g, const Vertex& source, std::size_t component, std::vector<Vertex>* otherVertices) const {
		EdgeIterator begin, end;
		Vertex targetNode;
		boost::tie(begin, end) = boost::out_edges(source, g);
		for (; begin != end; ++begin) {
			targetNode = target(*begin, g);
			if (g[targetNode].component == component) break;
			if (otherVertices != nullptr) {
				otherVertices->push_back(targetNode);
			}
		}
		assert(g[targetNode].component == component);
		if (otherVertices != nullptr) {
			for (; begin != end; ++begin) {
				Vertex v = target(*begin, g);
				if (g[v].component == component) continue;
				otherVertices->push_back(v);
			}
		}
		return targetNode;
	}
	
	template<class Settings>
	FormulaT LICModule<Settings>::buildCycleFormula(const Graph& g, const std::vector<Vertex>& cycle) const {
		FormulasT res;
		std::transform(cycle.begin(), cycle.end(), std::back_inserter(res), [&g](const Vertex& v){ return g[v].constraint; });
		return FormulaT(carl::FormulaType::AND, std::move(res));
	}
	
	template<class Settings>
	Answer LICModule<Settings>::analyzeCycle(const Graph& g, const Vertex& root) {
		Coefficient sum;
		Vertex cur = root;
		std::size_t component = g[cur].component;
		std::vector<Vertex> cycle; // Variables on the cycle
		std::vector<Vertex> edges; // Edges on the cycle
		std::vector<Vertex> others; // Variables adjacent to the cycle
		while (true) {
			cycle.push_back(cur);
			// Get edge node
			Vertex edgeNode = nextInComponent(g, cur, component);
			edges.push_back(edgeNode);
			// Get next variable node
			Vertex targetNode = nextInComponent(g, edgeNode, component, &others);
			sum += g[edgeNode].coeff;
			if (targetNode == root) break;
			cur = targetNode;
		}
		if (carl::isZero(sum.r)) {
			FormulaT origin = buildCycleFormula(g, edges);
			if (sum.strict) {
				// Sum is zero but there is a strict inequality -> UNSAT
				mInfeasibleSubsets.emplace_back(origin.subformulas().begin(), origin.subformulas().end());
				return False;
			} else {
				// Sum is zero and all inequalities are weak
				// -> Variables on the cycle 
				for (const auto& v: others) {
					FormulaT lemma(Poly(g[v].var), carl::Relation::EQ);
					addSubformulaToPassedFormula(lemma, origin);
				}
				for (std::size_t i = 1; i < cycle.size(); i++) {
					TermT a(g[cycle[i-1]].var);
					TermT b(g[cycle[i]].var);
					if (isSemiNegative(g[cycle[i-1]].var)) a = -a;
					if (isSemiNegative(g[cycle[i]].var)) b = -b;
					FormulaT lemma(a-b + g[edges[i-1]].coeff.r, carl::Relation::EQ);
					addSubformulaToPassedFormula(lemma, origin);
				}
				return True;
			}
		} else if (sum.r > 0) {
			std::cout << "What to do? sum > 0" << std::endl;
		} else if (sum.r < 0) {
			FormulaT origin = buildCycleFormula(g, edges);
			mInfeasibleSubsets.emplace_back(origin.subformulas().begin(), origin.subformulas().end());
			return False;
		}
		return True;
	}
}

#include "Instantiation.h"
