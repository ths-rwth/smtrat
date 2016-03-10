#pragma once

#include "../../logging.h"

#include "ModelVariable.h"
#include "ModelValue.h"
#include "ModelSubstitution.h"

namespace smtrat
{
	/// Data type for a assignment assigning a variable, represented as a string, a real algebraic number, represented as a string.
	/// Basically a wrapper around std::map.
	class Model {
	public:
		//using Map = std::unordered_map<ModelVariable,ModelValue>;
		using Map = std::map<ModelVariable,ModelValue>;
	private:
		Map mData;
		std::map<ModelVariable, std::size_t> mUsedInSubstitution;
	public:
		// Element access
		auto at(const Map::key_type& key) const -> decltype(mData.at(key)) {
			return mData.at(key);
		}
		
		// Iterators
		auto begin() const -> decltype(mData.begin()) {
			return mData.begin();
		}
		auto end() const -> decltype(mData.end()) {
			return mData.end();
		}
		// Capacity
		auto empty() const -> decltype(mData.empty()) {
			return mData.empty();
		}
		auto size() const -> decltype(mData.size()) {
			return mData.size();
		}
		// Modifiers
		void clear() {
			mData.clear();
		}
		template<typename P>
		auto insert(const P& pair) -> decltype(mData.insert(pair)) {
			return mData.insert(pair);
		}
		template<typename P>
		auto insert(Map::const_iterator it, const P& pair) -> decltype(mData.insert(it, pair)) {
			return mData.insert(it, pair);
		}
		template<typename... Args>
		auto emplace(const Map::key_type& key, Args&& ...args) -> decltype(mData.emplace(key,std::forward<Args>(args)...)) {
			return mData.emplace(key,std::forward<Args>(args)...);
		}
		template<typename... Args>
		auto emplace_hint(Map::const_iterator it, const Map::key_type& key, Args&& ...args) -> decltype(mData.emplace_hint(it, key,std::forward<Args>(args)...)) {
			return mData.emplace_hint(it, key,std::forward<Args>(args)...);
		}
		Map::iterator erase(const ModelVariable& variable) {
			return erase(mData.find(variable));
		}
		Map::iterator erase(const Map::iterator& it) {
			return erase(Map::const_iterator(it));
		}
		Map::iterator erase(const Map::const_iterator& it) {
			if (it == mData.end()) return mData.end();
			for (auto& m: mData) {
				const auto& val = m.second;
				if (!val.isSubstitution()) continue;
				const auto& subs = val.asSubstitution();
				if (subs->dependsOn(it->first)) {
					SMTRAT_LOG_DEBUG("smtrat.model", "Evaluating " << m.first << " ->  " << subs << " as " << it->first << " is removed from the model.");
					m.second = subs->evaluate(*this);
				}
			}
			return mData.erase(it);
		}
        void clean() {
            for (auto& m: mData) {
				const auto& val = m.second;
				if (!val.isSubstitution()) continue;
				const auto& subs = val.asSubstitution();
                SMTRAT_LOG_DEBUG("smtrat.model", "Evaluating " << m.first << " ->  " << subs << " as.");
                m.second = subs->evaluate(*this);
			}
        }
		// Lookup
		auto find(const Map::key_type& key) const -> decltype(mData.find(key)) {
			return mData.find(key);
		}
		auto find(const Map::key_type& key) -> decltype(mData.find(key)) {
			return mData.find(key);
		}
		
		// Additional (w.r.t. std::map)
		template<typename T>
		void assign(const Map::key_type& key, const T& t) {
			auto it = mData.find(key);
			if (it == mData.end()) mData.emplace(key, t);
			else it->second = t;
		}
		void merge(const Model& model, bool overwrite = false) {
			for (const auto& m: model) {
				auto res = mData.insert(m);
				if (overwrite) {
					if (!res.second) {
						res.first->second = m.second;
					}
				} else {
					assert(res.second);
				}
			}
		}
	};
	
}

#include "ModelSubstitution.h"
