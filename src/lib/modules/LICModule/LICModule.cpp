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
		SMTRAT_LOG_DEBUG("smtrat.lic", "Obtained the following bounds: " << std::endl << mBounds);
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
				mBounds.addBound(f.constraint(), f);
				if (!f.constraint().isBound()) {
					mConstraints.insert(f.constraint());
				}
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), invertRelation(c.relation()));
					mBounds.addBound(newC, f);
					if (!newC.isBound()) {
						mConstraints.insert(newC);
					}
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
				mBounds.removeBound(f.constraint(), f);
				if (!f.constraint().isBound()) {
					mConstraints.erase(f.constraint());
				}
				break;
			case carl::FormulaType::NOT: {
				if (f.subformula().getType() == carl::FormulaType::CONSTRAINT) {
					const ConstraintT& c = f.subformula().constraint();
					ConstraintT newC(c.lhs(), invertRelation(c.relation()));
					mBounds.removeBound(newC, f);
					if (!newC.isBound()) {
						mConstraints.erase(newC);
					}
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
		
		TermT src;
		std::vector<TermT> dest;
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
			SMTRAT_LOG_INFO("smtrat.lic", "Dumping resulting graph to " << Settings::dotFilename);
			VertexPropertyWriter vpw(graph);
			std::ofstream out(Settings::dotFilename);
			boost::write_graphviz(out, graph, vpw);
			out.close();
			
			SMTRAT_LOG_INFO("smtrat.lic", "Graph is:");
			SMTRAT_LOG_INFO("smtrat.lic", "components: " << component);
			SMTRAT_LOG_INFO("smtrat.lic", "discover time: " << discover_time);
		}
		
		for (const auto& c: classes) {
			if (c.second == 1) continue;
			Answer a = analyzeCycle(graph, c.first);
			if (a == False) return False;
		}
		return True;
	}
	
	template<class Settings>
	bool LICModule<Settings>::isSuitable(const ConstraintT& c, TermT& src, std::vector<TermT>& dest, Coefficient& coeff) {
		SMTRAT_LOG_FUNC("smtrat.lic", c);
		bool invert = false;
		src = TermT();
		dest.clear();
		coeff.strict = false;
		coeff.r = 0;

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
		Poly p = c.lhs();
		if (invert) p = -p;

		for (const auto& term: p) {
			if (term.isConstant()) {
				coeff.r += term.coeff();
				continue;
			}
			if (isZero(term)) {
				SMTRAT_LOG_WARN("smtrat.lic", "Term " << term << " is zero. We'll ignore it.");
				continue;
			}
			if (isSemiPositive(term)) {
				if (!src.isZero()) {
					SMTRAT_LOG_TRACE("smtrat.lic", "No: Already has a source, but " << term << " was found.");
					return false;
				}
				src = term;
			} else if (isSemiNegative(term)) {
				dest.push_back(-term);
			} else {
				SMTRAT_LOG_TRACE("smtrat.lic", "No: Has indefinite term " << term << ".");
				return false;
			}
		}
		if (dest.empty()) {
			SMTRAT_LOG_TRACE("smtrat.lic", "No: No destinations were found.");
			return false;
		}
		SMTRAT_LOG_TRACE("smtrat.lic", "Yes: " << src << " -> " << dest << " with coefficient " << coeff << ".");
		return true;
	}
	
	template<class Settings>
	typename LICModule<Settings>::VertexMap::mapped_type LICModule<Settings>::getVertex(Graph& g, VertexMap& vm, const TermT& t) const {
		auto it = vm.find(t);
		if (it != vm.end()) return it->second;
		auto res = boost::add_vertex(g);
		g[res].term = t;
		vm.emplace(t, res);
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
					FormulaT lemma(Poly(g[v].term), carl::Relation::EQ);
					SMTRAT_LOG_DEBUG("smtrat.lic", "Deducted " << lemma);
					addSubformulaToPassedFormula(lemma, origin);
				}
				for (std::size_t i = 1; i < cycle.size(); i++) {
					const TermT& a = g[cycle[i-1]].term;
					const TermT& b = g[cycle[i]].term;
					FormulaT lemma(a - b + g[edges[i-1]].coeff.r, carl::Relation::EQ);
					SMTRAT_LOG_DEBUG("smtrat.lic", "Deducted " << lemma);
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
