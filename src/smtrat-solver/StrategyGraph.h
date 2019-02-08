#pragma once

#include <memory>
#include <set>
#include <tuple>
#include <vector>

#include <smtrat-common/smtrat-common.h>
#include <smtrat-solver/Module.h>

namespace smtrat {
	
	typedef bool (*ConditionEvaluation)( carl::Condition );
	bool isCondition( carl::Condition _condition );
	
	struct AbstractModuleFactory {
		virtual ~AbstractModuleFactory() = default;
		virtual Module* create(const ModuleInput* _formula, Conditionals& _conditionals, Manager* const _manager) = 0;
		virtual std::string moduleName() const = 0;
	};

	template<typename Module>
	struct ModuleFactory: public AbstractModuleFactory {
	public:
		ModuleFactory(): AbstractModuleFactory() {}
		Module* create(const ModuleInput* _formula, Conditionals& _conditionals, Manager* const _manager) {
			return new Module(_formula, _conditionals, _manager);
		}
		std::string moduleName() const {
			return Module::SettingsType::moduleName;
		}
	};

	template<typename Module>
	inline std::ostream& operator<<(std::ostream& os, const ModuleFactory<Module>& mf) {
		return os << mf.moduleName();
	}

	typedef std::function<bool(carl::Condition)> ConditionFunction;
	class BackendLink {
	private:
		std::size_t mTarget;
		std::size_t mPriority;
		ConditionFunction mCondition;
	public:
		BackendLink(std::size_t target, std::size_t priority, const ConditionFunction& cf): mTarget(target), mPriority(priority), mCondition(cf) {}
		
		bool checkCondition(const carl::Condition& c) const {
			return mCondition(c);
		}
		std::size_t getTarget() const {
			return mTarget;
		}
		std::size_t getPriority() const {
			return mPriority;
		}
		
		bool operator<(const BackendLink& rhs) const {
			return mPriority < rhs.mPriority;
		}
		
		BackendLink& priority(std::size_t p) {
			mPriority = p;
			return *this;
		}
		template<typename T>
		BackendLink& condition(const T& f) {
			mCondition = ConditionFunction(f);
			return *this;
		}
		BackendLink& id(std::size_t& id) {
			id = mTarget;
			return *this;
		}
	};
	
	class StrategyGraph {
	public:
		static bool TrueCondition(const carl::Condition& c) {
			return carl::PROP_TRUE <= c;
		}
	private:

		std::vector<std::unique_ptr<AbstractModuleFactory>> mVertices;
		std::vector<std::vector<BackendLink>> mEdges;
		bool mHasBranches = false;
		std::size_t mNumberOfBranches = 1;
		std::size_t nextPriority = 1;
		std::size_t mRoot = 0;
		
		std::size_t newVertex(std::unique_ptr<AbstractModuleFactory> factory, const std::initializer_list<BackendLink>& backends) {
			//SMTRAT_LOG_DEBUG("smtrat.strategygraph", "Creating vertex with " << backends.size() << " backends");
			//SMTRAT_LOG_DEBUG("smtrat.strategygraph", "Current vertices: " << mVertices.size() << " vs " << mEdges.size());
			assert(mVertices.size() == mEdges.size());
			mVertices.push_back(std::move(factory));
			mEdges.emplace_back(backends);
			if (backends.size() > 1) {
				mHasBranches = true;
				mNumberOfBranches += backends.size() - 1;
			}
			return mVertices.size() - 1;
		}
		std::size_t getPriority(std::size_t priority) {
			if (priority == 0) priority = nextPriority;
			if (priority >= nextPriority) nextPriority = priority + 1;
			return priority;
		}
		
		void printAsTree(std::ostream& os, std::size_t vertex, std::set<std::size_t>& history, const std::string& indent = "") const {
			std::string moduleName = "Module";
			if (mVertices[vertex] != nullptr) moduleName = mVertices[vertex]->moduleName();
			if (history.count(vertex) > 0) {
				os << indent << moduleName << " (" << vertex << ") Backlink"<< std::endl;
			} else {
				os << indent << moduleName << " (" << vertex << ")"<< std::endl;
				history.insert(vertex);
				for (const auto& backend: mEdges[vertex]) {
					printAsTree(os, backend.getTarget(), history, indent + "    ");
				}
			}
		}
		
	public:
		StrategyGraph(): mVertices(), mEdges() {
			assert(mVertices.size() == mEdges.size());
		}
		
		template<typename Module>
		BackendLink addBackend(const std::initializer_list<BackendLink>& backends) {
			std::size_t id = newVertex(std::unique_ptr<ModuleFactory<Module>>(new ModuleFactory<Module>()), backends);
			for (auto& backend: mEdges[id]) {
				backend.priority(getPriority(backend.getPriority()));
			}
			SMTRAT_LOG_DEBUG("smtrat.strategygraph", "Adding backend " << id);
			return BackendLink(id, 0, TrueCondition);
		}
		
		BackendLink& addEdge(std::size_t from, std::size_t to) {
			assert(from < mEdges.size());
			if (!mEdges[from].empty()) mHasBranches = true;
			mEdges[from].emplace_back(to, 0, TrueCondition);
			return mEdges[from].back();
		}
		
		std::size_t addRoot(const std::initializer_list<BackendLink>& backends) {
			return mRoot = newVertex(nullptr, backends);
		}
		
		bool hasBranches() const {
			assert(mHasBranches == (mNumberOfBranches > 1));
			return mHasBranches;
		}
		std::size_t numberOfBranches() const {
			assert(mHasBranches == (mNumberOfBranches > 1));
			return mNumberOfBranches;
		}
		std::size_t getRoot() const {
			return mRoot;
		}
		
		std::set<std::pair<thread_priority,AbstractModuleFactory*>> getBackends(std::size_t vertex, const carl::Condition& condition) const {
			std::set<std::pair<thread_priority,AbstractModuleFactory*>> res;
			SMTRAT_LOG_DEBUG("smtrat.strategygraph", "Getting backends for vertex " << vertex);
			assert(vertex < mEdges.size());
			for (const auto& it: mEdges[vertex]) {
				if (it.checkCondition(condition)) {
					SMTRAT_LOG_DEBUG("smtrat.strategygraph", "\tfound " << it.getTarget());
					assert(mVertices[it.getTarget()] != nullptr);
					res.emplace(thread_priority(it.getPriority(), it.getTarget()), mVertices[it.getTarget()].get());
				}
			}
			return res;
		}
		
		friend std::ostream& operator<<(std::ostream& os, const StrategyGraph& sg) {
			std::set<std::size_t> history;
			sg.printAsTree(os, sg.mRoot, history);
			return os;
		}
	};
}
