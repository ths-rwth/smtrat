#pragma once

#include "../Common.h"

namespace smtrat::cad {

namespace preprocessor {

struct Origins {
	std::map<FormulaT, std::vector<std::vector<FormulaT>>> mOrigins;

	static std::size_t complexity(const std::vector<FormulaT>& origin) {
		return std::accumulate(origin.begin(), origin.end(), 0, 
			[](std::size_t i, const auto& f){ return i + f.complexity(); }
		);
	}

	void cleanOrigins(const FormulaT& f) {
		for (auto it = mOrigins.begin(); it != mOrigins.end(); ) {
			for (auto oit = it->second.begin(); oit != it->second.end(); ) {
				auto keep = std::find(oit->begin(), oit->end(), f) == oit->end();
				if (keep) ++oit;
				else oit = it->second.erase(oit);
			}
			if (it->second.empty()) {
				it = mOrigins.erase(it);
			} else {
				++it;
			}
		}
	}

	void add(const FormulaT& f, const std::vector<FormulaT>& origin) {
		auto it = mOrigins.find(f);
		if (it == mOrigins.end()) {
			mOrigins.emplace(f, std::vector<std::vector<FormulaT>>({origin}));
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding new origins " << f << " -> " << origin);
			return;
		}
		it->second.emplace_back(origin);
		std::sort(it->second.begin(), it->second.end(),
			[](const auto& a, const auto& b){
				if (a.size() != b.size()) return a.size() < b.size();
				return complexity(a) < complexity(b);
			}
		);
	}

	void remove(const FormulaT& f) {
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Erasing " << f << " from Origins: " << mOrigins);
		mOrigins.erase(f);
		cleanOrigins(f);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Result Origins: " << mOrigins);
	}

	const std::vector<FormulaT>& get(const FormulaT& f) const {
		auto it = mOrigins.find(f);
		assert(it != mOrigins.end());
		return it->second.front();
	}

	bool resolve(std::set<FormulaT>& conflict) const {
		bool didReplacement = false;
		for (const auto& origins: mOrigins) {
			const auto& c = origins.second.front(); 
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Considering origin " << origins.first << " -> " << c);
			if (c.size() == 1 && c.front() == origins.first) {
				continue;
			}
			if (conflict.erase(origins.first) > 0) {
				conflict.insert(c.begin(), c.end());
				didReplacement = true;
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Replaced " << origins.first << " by origins " << c);
			}
		}
		return didReplacement;
	}
};

class AssignmentCollector {
public:
	/// Result of an assignment collection.
	/// true: new assignments were found
	/// false: no new assignments were found
	/// constraint: found direct conflict
	using CollectionResult = std::variant<bool,ConstraintT>;
private:
	Model& mModel;
	/// Reasons for the assignment of variables.
	std::map<carl::Variable, ConstraintT> mReasons;
	std::map<ConstraintT, carl::Variable> mConstraints;

	bool extractValueAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		carl::Variable v;
		Rational r;
		bool foundAssignment = false;
		for (auto it = constraints.begin(); it != constraints.end(); ) {
			if (it->second.getAssignment(v, r) && mModel.find(v) == mModel.end()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << r);
				mModel.emplace(v, r);
				mReasons.emplace(v, it->first);
				mConstraints.emplace(it->first, v);
				it = constraints.erase(it);
				foundAssignment = true;
			} else {
				SMTRAT_LOG_TRACE("smtrat.cad.pp", "No assignment from " << it->second);
				++it;
			}
		}
		return foundAssignment;
	}
	bool extractParametricAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		carl::Variable v;
		Poly r;
		bool foundAssignment = false;
		for (auto it = constraints.begin(); it != constraints.end(); ) {
			if (it->second.getSubstitution(v, r) && mModel.find(v) == mModel.end()) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Newly extracted " << v << " = " << r);
				mModel.emplace(v, carl::createSubstitution<Rational,Poly,ModelPolynomialSubstitution>(r));
				mReasons.emplace(v, it->first);
				mConstraints.emplace(it->first, v);
				it = constraints.erase(it);
				foundAssignment = true;
				break;
			} else {
				SMTRAT_LOG_TRACE("smtrat.cad.pp", "No assignment from " << it->second);
				++it;
			}
		}
		return foundAssignment;
	}

	bool extractAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
		if (extractValueAssignments(constraints)) return true;
		return extractParametricAssignments(constraints);
	}

	std::optional<ConstraintT> simplify(std::map<ConstraintT, ConstraintT>& constraints) {
		for (auto& c: constraints) {
			carl::model::substituteIn(c.second, mModel);
			if (c.second.isConsistent() == 0) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Simplification found conflict in " << c.first << " (" << c.second << ")");
				return c.first;
			}
		}
		return std::nullopt;
	}
public:

	AssignmentCollector(Model& model): mModel(model) {}

	const auto& reasons() const {
		return mReasons;
	}
	auto& reasons() {
		return mReasons;
	}
	const auto& constraints() const {
		return mConstraints;
	}
	auto& constraints() {
		return mConstraints;
	}

	CollectionResult collect(std::map<ConstraintT, ConstraintT>& constraints) {
		if (auto c = simplify(constraints); c) {
			return *c;
		}
		bool foundNew = false;
		bool continueSearch = true;
		while (continueSearch) {
			continueSearch = extractAssignments(constraints);
			SMTRAT_LOG_TRACE("smtrat.cad.pp", "Extracted assignments " << mModel << " from " << constraints);
			if (auto c = simplify(constraints); c) {
				return *c;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After simplication with " << mModel << ": " << constraints);
			foundNew = foundNew || continueSearch;
		}
		return foundNew;
	}
};

class ResultantRule {
private:
	const std::vector<carl::Variable>& mVars;
	std::vector<ConstraintT> mConstraints;
	std::vector<std::vector<UPoly>> mData;
	std::vector<ConstraintT> mNewECs;
	Origins& mOrigins;

	bool addPoly(const Poly& poly) {
		if (poly.isZero()) return true;
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding poly " << poly << " under ordering " << mVars);
		std::size_t level = 0;
		UPoly p = poly.toUnivariatePolynomial(mVars[level]);
		while (p.isConstant()) {
			++level;
			p = poly.toUnivariatePolynomial(mVars[level]);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Inserting " << p << " into level " << level);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Into " << mData);
		mData[level].emplace_back(p);
		return true;
	}

	bool addPoly(const UPoly& poly, std::size_t level, const std::vector<FormulaT>& origin) {
		if (poly.isZero()) return true;
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding poly " << poly << " under ordering " << mVars);
		Poly mp(poly);
		UPoly p = poly;
		assert(p.mainVar() == mVars[level]);
		while (p.isConstant()) {
			++level;
			p = mp.toUnivariatePolynomial(mVars[level]);
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Inserting " << p << " into level " << level);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Into " << mData);
		mData[level].emplace_back(p);
		ConstraintT cons(mp, carl::Relation::EQ);
		mOrigins.add(FormulaT(mp, carl::Relation::EQ), origin);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Origins: " << mOrigins.mOrigins);
		mNewECs.emplace_back(cons);
		if (cons.isConsistent() == 0) return false;
		return true;
	}

	std::optional<std::vector<FormulaT>> computeResultants(std::size_t level) {
		for (std::size_t pid = 0; pid < mData[level].size(); ++pid) {
			for (std::size_t qid = pid + 1; qid < mData[level].size(); ++qid) {
				auto r = projection::resultant(mVars[level + 1], mData[level][pid], mData[level][qid]);
				std::vector<FormulaT> origin;
				const auto& op = mOrigins.get(FormulaT(Poly(mData[level][pid]), carl::Relation::EQ));
				origin.insert(origin.end(), op.begin(), op.end());
				const auto& oq = mOrigins.get(FormulaT(Poly(mData[level][qid]), carl::Relation::EQ));
				origin.insert(origin.end(), oq.begin(), oq.end());
				if (!addPoly(r, level + 1, origin)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Found direct conflict due to " << origin);
					return origin;
				}
			}
		}
		return std::nullopt;
	}

public:
	ResultantRule(Origins& origins, const std::vector<carl::Variable>& vars):
		mOrigins(origins),
		mVars(vars)
	{}
	
	std::optional<std::vector<FormulaT>> compute(const std::map<ConstraintT,ConstraintT>& constraints) {
		mConstraints.clear();
		mData.assign(mVars.size(), {});
		mNewECs.clear();
		for (const auto& c: constraints) {
			mConstraints.emplace_back(c.first);
			if (!addPoly(c.second.lhs())) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Found direct conflict due to " << c.first);
				return std::vector<FormulaT>({ FormulaT(c.first) });
			}
		}

		for (std::size_t level = 0; level < mData.size() - 1; ++level) {
			auto conflict = computeResultants(level);
			if (conflict) return conflict;
		}
		return std::nullopt;
	}

	const auto& getNewECs() const {
		return mNewECs;
	}
};

struct ConstraintUpdate {
	std::vector<ConstraintT> toAdd;
	std::vector<ConstraintT> toRemove;
};

}

class CADPreprocessor {
public:
	friend std::ostream& operator<<(std::ostream& os, const CADPreprocessor& cadpp);
private:
	/// The model used for variable elimination.
	Model mModel;
	/// Variable ordering.
	const std::vector<carl::Variable>& mVars;
	/// Origins of new formulas.
	preprocessor::Origins mOrigins;
	/// The assignment collector.
	preprocessor::AssignmentCollector mAssignments;
	/// The resultant rule.
	preprocessor::ResultantRule mResultants;

	/// Equalities from the input.
	std::vector<ConstraintT> mEqualities;
	/// Inequalities from the input.
	std::map<ConstraintT, ConstraintT> mInequalities;
	/// Derived set of equalities, essentially mEqualities - mModel.
	std::map<ConstraintT, ConstraintT> mDerivedEqualities;


	std::optional<std::set<FormulaT>> mConflict;

	void resetCached() {
		mDerivedEqualities.clear();
		mModel.clear();
		mAssignments.reasons().clear();
		mAssignments.constraints().clear();
		for (auto& i: mInequalities) {
			i.second = i.first;
		}
	}

	void removeEquality(const ConstraintT& c) {
		auto it = std::remove(mEqualities.begin(), mEqualities.end(), c);
		mEqualities.erase(it, mEqualities.end());
		resetCached();
	}

	bool addEqualities(const std::vector<ConstraintT>& constraints) {
		bool addedNew = false;
		for (const auto& c: constraints) {
			if (mAssignments.constraints().find(c) != mAssignments.constraints().end()) continue;
			if (mDerivedEqualities.try_emplace(c, c).second) {
				addedNew = true;
			}
		}
		return addedNew;
	}

	std::vector<ConstraintT> collectDerivedEqualities() const {
		std::vector<ConstraintT> cur;
		for (const auto& c: mDerivedEqualities) {
			cur.emplace_back(c.second);
		}
		return cur;
	}

	/**
	 * Replace constraints that have been modified by its origins in the given conflict.
	 */
	bool collectOriginsOfConflict(std::set<FormulaT>& conflict, const std::map<ConstraintT, ConstraintT>& constraints) const {
		bool didReplacement = false;
		for (const auto& c: constraints) {
			if (c.first == c.second) continue;
			if (conflict.erase(FormulaT(c.second)) > 0) {
				conflict.emplace(c.first);
				didReplacement = true;
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Replaced " << c.second << " by origin " << c.first);
			}
		}
		return didReplacement;
	}

	bool addModelToConflict(std::set<FormulaT>& conflict, carl::Variables& added) const {
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Adding necessary parts of model to conflict: " << conflict);
		carl::Variables vars;
		bool changed = false;
		for (const auto& f: conflict) f.allVars(vars);
		while (!vars.empty()) {
			carl::Variables newvars;
			for (auto v: vars) {
				auto it = mAssignments.reasons().find(v);
				if (it == mAssignments.reasons().end()) continue;
				if (added.find(v) != added.end()) continue;
				added.insert(v);
				auto cit = conflict.emplace(it->second);
				changed = true;
				if (cit.second) {
					cit.first->allVars(newvars);
					SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Added " << it->second << " to conflict.");
				}
			}
			vars = newvars;
		}
		return changed;
	}

public:
	CADPreprocessor(const std::vector<carl::Variable>& vars):
		mModel(),
		mVars(vars),
		mAssignments(mModel),
		mResultants(mOrigins, mVars)
	{}

	void addConstraint(const ConstraintT& c) {
		if (c.relation() == carl::Relation::EQ) {
			mEqualities.emplace_back(c);
		} else {
			mInequalities.emplace(c, c);
		}
		mOrigins.add(FormulaT(c), { FormulaT(c) });
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Origins: " << mOrigins.mOrigins);
		SMTRAT_LOG_TRACE("smtrat.cad.pp", "Added " << c << " to " << std::endl << *this);
	}

	void removeConstraint(const ConstraintT& c) {
		if (c.relation() == carl::Relation::EQ) {
			removeEquality(c);
		} else {
			auto it = mInequalities.find(c);
			assert(it != mInequalities.end());
			mInequalities.erase(it);
		}
		mOrigins.remove(FormulaT(c));
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Origins: " << mOrigins.mOrigins);
		SMTRAT_LOG_TRACE("smtrat.cad.pp", "Removed " << c << " from " << std::endl << *this);
	}

	/**
	 * Performs the preprocessing.
	 * Return false if a direct conflict was found, true otherwise.
	 */
	bool preprocess() {
		std::vector<ConstraintT> cur = mEqualities;
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Starting with:" << std::endl << *this);
		while (addEqualities(cur)) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collecting assignments from:" << std::endl << *this);
			auto collectResult = mAssignments.collect(mDerivedEqualities);
			if (std::holds_alternative<ConstraintT>(collectResult)) {
				mConflict = { FormulaT(std::get<ConstraintT>(collectResult)) };
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			}
			assert(std::holds_alternative<bool>(collectResult));
			if (std::get<bool>(collectResult) == false) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "No further assignments.");
				break;
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collected assignments:" << std::endl << *this);
			
			auto conflict = mResultants.compute(mDerivedEqualities);
			if (conflict.has_value()) {
				mConflict = std::set<FormulaT>(conflict->begin(), conflict->end());
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
			} else {
				cur = mResultants.getNewECs();
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Computed resultants:" << std::endl << *this << std::endl << "-> " << cur);
			}
		}
		for (auto& c: mInequalities) {
			carl::model::substituteIn(c.second, mModel);
			if (c.second.isConsistent() == 0) {
				mConflict = { FormulaT(c.first) };
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After preprocessing:" << std::endl << *this);
		return true;
	}

	const Model& model() const {
		return mModel;
	}

	template<typename Map>
	preprocessor::ConstraintUpdate result(const Map& oldC) const {
		std::set<ConstraintT> newC;
		for (const auto& c: mInequalities) {
			if (c.second.isConsistent() == 1) continue;
			newC.insert(c.second);
		}
		for (const auto& c: mDerivedEqualities) {
			if (c.second.isConsistent() == 1) continue;
			newC.insert(c.second);
		}

		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Old state:" << std::endl << oldC);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "New state:" << std::endl << newC);

		std::vector<ConstraintT> toAdd;
		std::vector<ConstraintT> toRemove;

		for (const auto& c: newC) {
			if (oldC.find(c) == oldC.end()) toAdd.emplace_back(c);
		}
		for (const auto& c: oldC) {
			if (newC.find(c.first) == newC.end()) toRemove.emplace_back(c.first);
		}

		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To add:" << std::endl << toAdd);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "To remove:" << std::endl << toRemove);

		return {toAdd, toRemove};
	}

	std::set<FormulaT> getConflict() const {
		assert(mConflict);
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Building MIS from immediate conflict " << *mConflict);
		std::set<FormulaT> res = *mConflict;
		postprocessConflict(res);
		return res;
	}

	void postprocessConflict(std::set<FormulaT>& mis) const {
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Postprocessing conflict: " << mis << " based on" << std::endl << *this);
		if (collectOriginsOfConflict(mis, mInequalities)) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resolved inequalities: " << mis);
		}
		bool changed = true;
		carl::Variables modelAdded;
		while (changed) {
			changed = false;
			if (collectOriginsOfConflict(mis, mDerivedEqualities)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resolved equalities: " << mis);
				changed = true;
			}
			if (mOrigins.resolve(mis)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resolved resultants: " << mis);
				changed = true;
			}
			if (addModelToConflict(mis, modelAdded)) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resolved model: " << mis);
				changed = true;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Postprocessed conflict: " << mis);
	}
};

inline std::ostream& operator<<(std::ostream& os, const CADPreprocessor& cadpp) {
	os << "Equalities: " << cadpp.mEqualities << std::endl;
	os << "Inequalities: " << cadpp.mInequalities << std::endl;
	os << "Derived: " << cadpp.mDerivedEqualities << std::endl;
	os << "Model: " << cadpp.mModel << std::endl;
	os << "Reasons: " << cadpp.mAssignments.reasons() << std::endl;
	return os;
}



}