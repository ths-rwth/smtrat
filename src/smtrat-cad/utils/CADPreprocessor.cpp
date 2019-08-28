#include "CADPreprocessor.h"

namespace smtrat::cad {

const bool CADPreprocessorSettings::dummy = CADPreprocessorSettings::register_hook();

namespace preprocessor {

inline std::size_t complexity(const std::vector<FormulaT>& origin) {
    return std::accumulate(origin.begin(), origin.end(), static_cast<std::size_t>(0), 
        [](std::size_t i, const auto& f){ return i + f.complexity(); }
    );
}

void Origins::cleanOrigins(const FormulaT& f) {
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

void Origins::add(const FormulaT& f, const std::vector<FormulaT>& origin) {
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

void Origins::remove(const FormulaT& f) {
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Erasing " << f << " from Origins: " << mOrigins);
    mOrigins.erase(f);
    cleanOrigins(f);
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Result Origins: " << mOrigins);
}

const std::vector<FormulaT>& Origins::get(const FormulaT& f) const {
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Looking for " << f << " in Origins: " << mOrigins);
    auto it = mOrigins.find(f);
    assert(it != mOrigins.end());
    return it->second.front();
}

bool Origins::resolve(std::set<FormulaT>& conflict) const {
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

bool AssignmentCollector::extractValueAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
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
bool AssignmentCollector::extractParametricAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
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

bool AssignmentCollector::extractAssignments(std::map<ConstraintT, ConstraintT>& constraints) {
    if (extractValueAssignments(constraints)) return true;
    return extractParametricAssignments(constraints);
}

AssignmentCollector::CollectionResult AssignmentCollector::simplify(std::map<ConstraintT, ConstraintT>& constraints) {
	bool changed = false;
    for (auto& c: constraints) {
        auto tmp = carl::model::substitute(c.second, mModel);
		if (tmp != c.second && constraints.find(tmp) == constraints.end()) {
			changed = true;
			c.second = tmp;
		}
        if (c.second.isConsistent() == 0) {
            SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Simplification found conflict in " << c.first << " (" << c.second << ")");
            return c.first;
        }
    }
    return changed;
}

AssignmentCollector::CollectionResult AssignmentCollector::collect(std::map<ConstraintT, ConstraintT>& constraints) {
	auto sres = simplify(constraints);
	if (std::holds_alternative<ConstraintT>(sres)) {
		return sres;
	}
	assert(std::holds_alternative<bool>(sres));
    bool foundNew = std::get<bool>(sres);
    bool continueSearch = true;
    while (continueSearch) {
        continueSearch = extractAssignments(constraints);
        SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Extracted assignments " << mModel << " from " << constraints);
		auto sres = simplify(constraints);
		if (std::holds_alternative<ConstraintT>(sres)) {
			return sres;
		}
		assert(std::holds_alternative<bool>(sres));
        SMTRAT_LOG_DEBUG("smtrat.cad.pp", "After simplification with " << mModel << ": " << constraints);
        foundNew = foundNew || continueSearch || std::get<bool>(sres);
    }
    return foundNew;
}

bool ResultantRule::addPoly(const Poly& poly) {
    if (isZero(poly)) return true;
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

bool ResultantRule::addPoly(const UPoly& poly, std::size_t level, const std::vector<FormulaT>& origin) {
    if (isZero(poly)) return true;
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

std::optional<std::vector<FormulaT>> ResultantRule::computeResultants(std::size_t level) {
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

std::optional<std::vector<FormulaT>> ResultantRule::compute(const std::map<ConstraintT,ConstraintT>& constraints) {
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
	SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Done.");
    return std::nullopt;
}

}

void CADPreprocessor::resetCached() {
    mDerivedEqualities.clear();
    mModel.clear();
    mAssignments.reasons().clear();
    mAssignments.constraints().clear();
    for (auto& i: mInequalities) {
        i.second = i.first;
    }
}

void CADPreprocessor::removeEquality(const ConstraintT& c) {
    auto it = std::remove(mEqualities.begin(), mEqualities.end(), c);
    mEqualities.erase(it, mEqualities.end());
    resetCached();
}

bool CADPreprocessor::addEqualities(const std::vector<ConstraintT>& constraints) {
    bool addedNew = false;
    for (const auto& c: constraints) {
        if (mAssignments.constraints().find(c) != mAssignments.constraints().end()) continue;
        if (mDerivedEqualities.try_emplace(c, c).second) {
            addedNew = true;
        }
    }
    return addedNew;
}

std::vector<ConstraintT> CADPreprocessor::collectDerivedEqualities() const {
    std::vector<ConstraintT> cur;
    for (const auto& c: mDerivedEqualities) {
        cur.emplace_back(c.second);
    }
    return cur;
}

bool CADPreprocessor::collectOriginsOfConflict(std::set<FormulaT>& conflict, const std::map<ConstraintT, ConstraintT>& constraints) const {
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

bool CADPreprocessor::addModelToConflict(std::set<FormulaT>& conflict, carl::Variables& added) const {
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

void CADPreprocessor::addConstraint(const ConstraintT& c) {
    if (c.relation() == carl::Relation::EQ) {
        mEqualities.emplace_back(c);
    } else {
        mInequalities.emplace(c, c);
    }
    mOrigins.add(FormulaT(c), { FormulaT(c) });
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Origins: " << mOrigins.mOrigins);
    SMTRAT_LOG_TRACE("smtrat.cad.pp", "Added " << c << " to " << std::endl << *this);
}

void CADPreprocessor::removeConstraint(const ConstraintT& c) {
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

bool CADPreprocessor::preprocess() {
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Starting with:" << std::endl << *this);
	bool changed = addEqualities(mEqualities);
    while (changed) {
		changed = false;
		if (settings_cadpp().disable_variable_elimination) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Variable elimination is disabled");
		} else {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collecting assignments from:" << std::endl << *this);
			auto collectResult = mAssignments.collect(mDerivedEqualities);
			if (std::holds_alternative<ConstraintT>(collectResult)) {
				mConflict = { FormulaT(std::get<ConstraintT>(collectResult)) };
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			}
			assert(std::holds_alternative<bool>(collectResult));
			if (std::get<bool>(collectResult) == true) {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Collected assignments:" << std::endl << *this);
				for (const auto& de: mDerivedEqualities) {
					mOrigins.add(FormulaT(de.second), {FormulaT(de.first)});
				}
				changed = true;
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Origins are now:" << std::endl << mOrigins.mOrigins);

		if (settings_cadpp().disable_resultants) {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Resultant rule is disabled");
		} else {
			SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Computing Resultants from:" << std::endl << *this);
			auto conflict = mResultants.compute(mDerivedEqualities);
			if (conflict.has_value()) {
				mConflict = std::set<FormulaT>(conflict->begin(), conflict->end());
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Immediate conflict due to " << *mConflict);
				return false;
			} else {
				SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Computed resultants:" << std::endl << *this << std::endl << "-> " << mResultants.getNewECs());
				if (addEqualities(mResultants.getNewECs())) {
					changed = true;
				}
			}
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

std::set<FormulaT> CADPreprocessor::getConflict() const {
    assert(mConflict);
    SMTRAT_LOG_DEBUG("smtrat.cad.pp", "Building MIS from immediate conflict " << *mConflict);
    std::set<FormulaT> res = *mConflict;
    postprocessConflict(res);
    return res;
}

void CADPreprocessor::postprocessConflict(std::set<FormulaT>& mis) const {
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

}
