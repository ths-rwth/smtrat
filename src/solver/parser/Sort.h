/**
 * @file Sort.h
 * @author Gereon Kremer <gereon.kremer@cs.rwth-aachen.de>
 */

#pragma once

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include "carl/util/Singleton.h"
#include "carl/core/Variable.h"

namespace smtrat {
namespace parser {

class Sort {
private:
	std::string mName;
	std::vector<Sort> mParameters;
public:
	explicit Sort() {}
	explicit Sort(const std::string& name): mName(name) {}
	explicit Sort(const std::string& name, const std::vector<Sort>& parameters): mName(name), mParameters(parameters) {}
	
	std::size_t arity() const {
		return mParameters.size();
	}
	
	Sort replace(const std::map<std::string, Sort>& m) const {
		std::vector<Sort> v;
		v.reserve(mParameters.size());
		for (auto sd: mParameters) v.push_back(sd.replace(m));
		if (m.count(mName) > 0) return m.at(mName);
		else return Sort(mName, v);
	}
	
	friend std::ostream& operator<<(std::ostream& os, const Sort& sd) {
		if (sd.arity() == 0) os << sd.mName;
		else {
			os << "(" << sd.mName;
			for (auto p: sd.mParameters) os << " " << p;
			os << ")";
		}
		return os;
	}
	
	bool operator==(const Sort& s) const {
		if (mName != s.mName) return false;
		if (mParameters.size() != s.mParameters.size()) return false;
		for (std::size_t i = 0; i < mParameters.size(); i++) {
			if (this->mParameters[i] != s.mParameters[i]) return false;
		}
		return true;
	}
	bool operator!=(const Sort& s) const {
		return !(*this == s);
	}
	bool operator<(const Sort& s) const {
		if (mName < s.mName) return true;
		if (mParameters.size() != s.mParameters.size()) return (mParameters.size() < s.mParameters.size());
		for (std::size_t i = 0; i < mParameters.size(); i++) {
			if (mParameters[i] < s.mParameters[i]) return true;
		}
		return false;
	}
};

class SortManager : public carl::Singleton<SortManager> {
	friend carl::Singleton<SortManager>;
public:
	typedef std::pair<std::vector<std::string>, Sort> SortTemplate;
private:
	std::map<Sort, carl::VariableType> mInterpreted;
	std::map<std::string, unsigned> mDeclarations;
	std::map<std::string, SortTemplate> mDefinitions;
	
	SortManager() {
	}
public:
	bool declare(const std::string& name, unsigned arity) {
		if (this->mDeclarations.count(name) > 0) return false;
		this->mDeclarations[name] = arity;
		return true;
	}
	
	bool define(const std::string& name, const std::vector<std::string>& params, const Sort& s) {
		if (this->mDefinitions.count(name) > 0) return false;
		this->mDefinitions[name] = SortTemplate(params, s);
		return true;
	}
	
	std::size_t arity(const std::string& name) const {
		if (this->mDeclarations.count(name) > 0) {
			return this->mDeclarations.at(name);
		} else if (this->mDefinitions.count(name) > 0) {
			return this->mDefinitions.at(name).first.size();
		} else {
			std::cerr << "The sort " << name << " has not been declared or defined." << std::endl;
			assert(this->mDeclarations.count(name) > 0 || this->mDefinitions.count(name) > 0);
			return 0;
		}
	}
	
	Sort interpretedSort(const std::string& name, carl::VariableType type) {
		Sort s(name);
		mInterpreted[s] = type;
		return s;
	}
	bool isInterpreted(const Sort& s) const {
		return mInterpreted.find(s) != mInterpreted.end();
	}
	carl::VariableType interpretedType(const Sort& s) const {
		auto it = mInterpreted.find(s);
		assert(it != mInterpreted.end());
		return it->second;
	}
	
	Sort newSort(const std::string& name, const std::vector<Sort>& params) const {
		if (this->mDeclarations.count(name) > 0) {
			// Was declared, check the arity.
			unsigned arity = this->mDeclarations.at(name);
			if (arity == params.size()) return Sort(name, params);
			else {
				std::cerr << "The sort " << name << " was declared to have " << arity << " parameters, but only " << params.size() << " were given." << std::endl;
			}
		} else if (this->mDefinitions.count(name) > 0) {
			// Was defined, check the arity and replace the parameters in the defined sort.
			SortTemplate st = this->mDefinitions.at(name);
			if (st.first.size() == params.size()) {
				std::map<std::string, Sort> repl;
				for (unsigned i = 0; i < params.size(); i++) repl[st.first[i]] = params[i];
				return st.second.replace(repl);
			} else {
				std::cerr << "The sort " << name << " was defined to have " << st.first.size() << " parameters, but only " << params.size() << " were given." << std::endl;
			}
		} else {
			std::cerr << "The sort " << name << " has not been declared or defined." << std::endl;
		}
		return Sort("NO_SORT");
	}
};

inline Sort newSort(const std::string& name, const std::vector<Sort>& params) {
	return SortManager::getInstance().newSort(name, params);
}
inline Sort newSort(const std::string& name) {
	return SortManager::getInstance().newSort(name, {});
}

}
}