#include "FormulaEvaluationGraph.h"

#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/ran/Conversion.h>

#include <carl-common/util/streamingOperators.h>

#include "CoveringNGStatistics.h"

namespace smtrat::covering_ng::formula {
using carl::operator<<;

namespace formula_ds {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

void print(std::ostream& stream, const FormulaDB& db, const std::vector<FormulaState>& states, const FormulaID id, const std::size_t level) {
    std::visit(overloaded{
        [&](const TRUE&) {
            stream << std::string(level, ' ') << "TRUE";
        },
        [&](const FALSE&) {
            stream << std::string(level, ' ') << "FALSE";
        },
        [&](const NOT& c) {
            stream << std::string(level, ' ') << "NOT(" << std::endl;
            print(stream, db, states, c.subformula, level+1);
            stream << std::endl << std::string(level, ' ') << ")";
        },
        [&](const AND& c) {
            stream << std::string(level, ' ') << "AND(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, states, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const OR& c) {
            stream << std::string(level, ' ') << "OR(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, states, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const IFF& c) {
            stream << std::string(level, ' ') << "IFF(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, states, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const XOR& c) {
            stream << std::string(level, ' ') << "XOR(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, states, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const BOOL& c) {
            stream << std::string(level, ' ') << c.variable;
        },
        [&](const CONSTRAINT& c) {
            stream << std::string(level, ' ') << c.constraint;
        },
    }, db[id].content);

    std::size_t spacing = 50 - level;
    if (level > 50) spacing = 4;

    stream << std::string(spacing, ' ') << "id: " << id << " T: " << states[id].reasons_true << " F: " << states[id].reasons_false;
}

void log(const FormulaDB& db, const std::vector<FormulaState>& states, const FormulaID id) {
    std::stringstream ss;
    ss << std::endl;
    print(ss, db, states, id, 0);
    ss << std::endl;
    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", ss.str());
}


FormulaID to_formula_db(cadcells::datastructures::Projections& c, const FormulaT& f,  FormulaDB& db, VariableToFormula& vartof, std::map<std::size_t,FormulaID>& cache) {
    {
        auto cache_it = cache.find(f.id());
        if (cache_it != cache.end()) return cache_it->second;
    }

    assert(db.size() < std::numeric_limits<FormulaID>::max());

    if (f.id() > f.negated().id()) {
        auto child = to_formula_db(c,f.negated(),db,vartof, cache);
        db.emplace_back(NOT{ child });
        db[child].parents.insert((FormulaID)(db.size()-1));
        cache.emplace(f.id(), (FormulaID)(db.size()-1));
        return (FormulaID)(db.size()-1);
    }
    
    switch(f.type()) {
        case carl::FormulaType::ITE: {
            auto id = to_formula_db(c, FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, f.condition(), f.first_case()), FormulaT(carl::FormulaType::AND, f.condition().negated(), f.second_case())), db, vartof, cache);
            cache.emplace(f.id(), id);
            return id;
        }
        case carl::FormulaType::TRUE: {
            db.emplace_back(TRUE{ });
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::FALSE: {
            db.emplace_back(FALSE{ });
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::NOT: {
            auto child = to_formula_db(c,f.subformula(),db,vartof, cache);
            db.emplace_back(NOT{ child });
            db[child].parents.insert((FormulaID)(db.size()-1));
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::IMPLIES: {
            auto id = to_formula_db(c, FormulaT(carl::FormulaType::OR, f.premise().negated(), f.conclusion()), db, vartof, cache);
            cache.emplace(f.id(), id);
            return id;
        }
        case carl::FormulaType::AND: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(AND{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert((FormulaID)(db.size()-1));
            }
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::OR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(OR{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert((FormulaID)(db.size()-1));
            }
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::XOR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(XOR{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert((FormulaID)(db.size()-1));
            }
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::IFF: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(IFF{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert((FormulaID)(db.size()-1));
            }
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::CONSTRAINT: {
            auto bc = carl::convert<cadcells::Polynomial>(c.polys().context(), f.constraint().constr());
            db.emplace_back(CONSTRAINT{ c.polys()(bc) });
            auto var = bc.lhs().main_var();
            vartof.try_emplace(var).first->second.push_back((FormulaID)(db.size()-1));
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::BOOL: {
            db.emplace_back(BOOL{ f.boolean() });
            vartof.try_emplace(f.boolean()).first->second.push_back((FormulaID)(db.size()-1));
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        default: {
            assert(false);
            db.emplace_back(FALSE{});
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
    }
}

FormulaTree to_formula_tree(cadcells::datastructures::Projections& c, const FormulaT& f) {
    FormulaTree tree; 
    std::map<std::size_t,formula_ds::FormulaID> cache;
    tree.root = to_formula_db(c, f, tree.db, tree.vartof, cache);
    return tree;
}

enum CompareResult { SUBSET, SUPSET, EQ, NONE };

CompareResult compare(const FormulaState::Reason& a, const FormulaState::Reason& b) {
    if (a.size() == b.size()) {
        auto it_a = a.begin();
        auto it_b = b.begin();
        while (it_a != a.end() && *it_a == *it_b) {
            assert(it_b != b.end());
            it_a++;
            it_b++;
        }
        return (it_a == a.end()) ? EQ : NONE;
    } else if (a.size() < b.size()) {
        return std::includes(b.begin(), b.end(), a.begin(), a.end()) ? SUBSET : NONE;
    } else /* a.size() > b.size() */ {
        return std::includes(a.begin(), a.end(), b.begin(), b.end()) ? SUPSET : NONE;
    }
}

bool merge_reason(FormulaState::Reasons& set, const FormulaState::Reason& add) {
    for (auto s = set.begin(); s != set.end(); ) {
        switch(compare(*s,add)) {
            case SUBSET:
            case EQ:
                return false;
            case SUPSET:
                s = set.erase(s);
                break;
            case NONE:
            default:
                s++;
        }
    }
    set.push_back(add);
    return true;
}

bool merge_reasons(FormulaState::Reasons& set, const FormulaState::Reasons& adds) {
    FormulaState::Reasons to_add;
    for (const auto& add : adds) {
        bool redundant = false;
        for (auto s = set.begin(); s != set.end(); ) {
            switch(compare(*s,add)) {
                case SUBSET:
                case EQ:
                    s = set.end();
                    redundant = true;
                    break;
                case SUPSET:
                    s = set.erase(s);
                    break;
                case NONE:
                default:
                    s++;
            }
        }
        if (!redundant) to_add.push_back(add);
    }
    if (to_add.empty()) return false;
    else {
        set.insert(set.end(), to_add.begin(), to_add.end());
        return true;
    }
}

FormulaState::Reason merge(const FormulaState::Reason& a, const FormulaState::Reason& b) {
    FormulaState::Reason result;
    result.reserve(a.size()+b.size());
    auto first1 = a.begin();
    auto last1 = a.end();
    auto first2 = b.begin();
	auto last2 = b.end();
    auto d_first = std::back_inserter(result);
	for (; first1 != last1; ++d_first) {
		if (first2 == last2) {
            std::copy(first1, last1, d_first);
            return result;
        }
		if (*first2 < *first1) {
			*d_first = *first2;
			++first2;
		} else if (*first2 > *first1) {
			*d_first = *first1;
			++first1;
		} else {
            *d_first = *first1;
			++first1;
            ++first2;
        }
	}
    std::copy(first2, last2, d_first);
	result.shrink_to_fit();
    return result;
}

FormulaState::Reasons combine_reasons(const FormulaState::Reasons& a, const FormulaState::Reasons& b) {
    FormulaState::Reasons results;
    for (const auto& ar : a) {
        for (const auto& br : b) {
            merge_reason(results, merge(ar, br));
        }
    }
    return results;
}

struct FormulaClassification {
    std::vector<FormulaID> tru;
    std::vector<FormulaID> fals;
    std::vector<FormulaID> multi;
    std::vector<FormulaID> confl;
};

inline FormulaClassification classify_formulas(const FormulaTreeState& ts, const std::vector<FormulaID>& formulas) {
    FormulaClassification subs;
    for (const auto f : formulas) {
        auto sub_val = ts.valuation(f);
        if (sub_val == Valuation::FALSE) {
            subs.fals.push_back(f);
        } else if (sub_val == Valuation::TRUE) {
            subs.tru.push_back(f);
        } else if (sub_val == Valuation::MULTIVARIATE) {
            subs.multi.push_back(f);
        } else {
            assert(sub_val == Valuation::UNKNOWN);
            subs.confl.push_back(f);
        }
    }
    return subs;
}



void FormulaTreeState::propagate_consistency(FormulaID id) {
    if (valuation(id) == Valuation::UNKNOWN) {
        return;
    }

    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id);

    return std::visit(overloaded{
        [&](TRUE&) {},
        [&](FALSE&) {},
        [&](NOT& c) {
            auto val = valuation(id);
            auto sub_val = valuation(c.subformula);

            // upwards propagation
            if (sub_val == Valuation::TRUE) add_reasons_false(id, states[c.subformula].reasons_true);
            else if (sub_val == Valuation::FALSE) add_reasons_true(id, states[c.subformula].reasons_false);

            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE && sub_val == Valuation::MULTIVARIATE) { // sub_val == Valuation::MULTIVARIATE to avoid redundancies // TODO geht hierdurch was verloren?
                    add_reasons_false(c.subformula, states[id].reasons_true);
                } else if (val == Valuation::FALSE && sub_val == Valuation::MULTIVARIATE) {
                    add_reasons_true(c.subformula, states[id].reasons_false);
                }
            }
        },
        [&](AND& c) {
            auto val = valuation(id);
            auto subs = classify_formulas(*this, c.subformulas);

            // upwards propagation
            {
                if (!subs.fals.empty()) {
                    for (const auto& subformula : subs.fals) {
                        add_reasons_false(id, states[subformula].reasons_false);
                    }
                } else if (subs.confl.empty() && subs.multi.empty() && subs.fals.empty()) {
                    FormulaState::Reasons reasons;
                    reasons.emplace_back();
                    for (const auto& subformula : subs.tru) {
                        reasons = combine_reasons(reasons, states[subformula].reasons_true);
                    }
                    add_reasons_true(id, reasons);
                }
            }

            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    for (const auto subformula : subs.multi) { // avoids redundancy
                        add_reasons_true(subformula, states[id].reasons_true);
                    }
                } else if (val == Valuation::FALSE) {
                    if (subs.multi.size() == 1 && subs.confl.empty() && subs.fals.empty()) {
                        FormulaState::Reasons reasons = states[id].reasons_false;
                        for (const auto& subformula : subs.tru) {
                            reasons = combine_reasons(reasons, states[subformula].reasons_true);
                        }
                        add_reasons_false(*subs.multi.begin(), reasons);
                    }
                }
            }
        },
        [&](OR& c) {
            auto val = valuation(id);
            auto subs = classify_formulas(*this, c.subformulas);

            // upwards propagation
            {
                if (!subs.tru.empty()) {
                    for (const auto& subformula : subs.tru) {
                        add_reasons_true(id, states[subformula].reasons_true);
                    }
                } else if (subs.confl.empty() && subs.multi.empty() && subs.tru.empty()) {
                    FormulaState::Reasons reasons;
                    reasons.emplace_back();
                    for (const auto& subformula : subs.fals) {
                        reasons = combine_reasons(reasons, states[subformula].reasons_false);
                    }
                    add_reasons_false(id, reasons);
                }
            } 
            
            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    if (subs.multi.size() == 1 && subs.confl.empty() && subs.tru.empty()) {
                        FormulaState::Reasons reasons = states[id].reasons_true;
                        for (const auto& subformula : subs.fals) {
                            reasons = combine_reasons(reasons, states[subformula].reasons_false);
                        }
                        add_reasons_true(*subs.multi.begin(), reasons);
                    }
                } else if (val == Valuation::FALSE) {
                    for (const auto subformula : subs.multi) { // avoids redundancy
                        add_reasons_false(subformula, states[id].reasons_false);
                    }
                }
            }
        },
        [&](IFF& c) {
            auto subs = classify_formulas(*this, c.subformulas);
            auto val = valuation(id);

            // upwards propagation
            {
                if (!subs.tru.empty() && !subs.fals.empty()) {
                    FormulaState::Reasons reasons;
                    for (const auto t : subs.tru) {
                        for (const auto f : subs.fals) {
                            auto tmp = combine_reasons(states[t].reasons_true,states[f].reasons_false);
                            merge_reasons(reasons, tmp);
                        }
                    }
                    add_reasons_false(id, reasons);
                } else if (subs.multi.empty() && !subs.tru.empty()) {
                    FormulaState::Reasons reasons;
                    reasons.emplace_back();
                    for (const auto t : subs.tru) {
                        reasons = combine_reasons(reasons, states[t].reasons_true);
                    }
                    add_reasons_true(id, reasons);
                } else if (subs.multi.empty() && !subs.fals.empty()) {
                    FormulaState::Reasons reasons;
                    reasons.emplace_back();
                    for (const auto f : subs.fals) {
                        reasons = combine_reasons(reasons, states[f].reasons_false);
                    }
                    add_reasons_true(id, reasons);
                } 
            }
            
            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    for (const auto t : subs.tru) {
                        for (const auto sub : c.subformulas) {
                            auto sub_val = valuation(sub);
                            if (sub_val == Valuation::MULTIVARIATE) { // avoids redundancy
                                add_reasons_true(sub, combine_reasons(states[id].reasons_true, states[t].reasons_true));
                            }
                        }
                    }
                    for (const auto f : subs.fals) {
                        for (const auto sub : c.subformulas) {
                            auto sub_val = valuation(sub);
                            if (sub_val == Valuation::MULTIVARIATE) { // avoids redundancy
                                add_reasons_false(sub, combine_reasons(states[id].reasons_true, states[f].reasons_false));
                            }
                        }
                    }
                } else if (val == Valuation::FALSE) {
                    if (subs.multi.size() == 1 && (subs.tru.empty() || subs.fals.empty())) {
                        if (subs.tru.empty()) {
                            FormulaState::Reasons reasons = states[id].reasons_false;
                            for (const auto f : subs.fals) {
                                reasons = combine_reasons(reasons, states[f].reasons_false);
                            }
                            add_reasons_true(*subs.multi.begin(), reasons);
                        } else {
                            assert(subs.fals.empty());
                            FormulaState::Reasons reasons = states[id].reasons_false;
                            for (const auto t : subs.tru) {
                                reasons = combine_reasons(reasons, states[t].reasons_true);
                            }
                            add_reasons_false(*subs.multi.begin(), reasons);
                        }
                    }
                }
            }
        },
        [&](XOR& c) {
            auto val = valuation(id);
            auto subs = classify_formulas(*this, c.subformulas);

            if (subs.confl.empty() && (subs.multi.empty() || subs.multi.size() == 1)) {
                FormulaState::Reasons reasons;
                reasons.emplace_back();
                for (const auto subformula : subs.tru) {
                    reasons = combine_reasons(reasons, states[subformula].reasons_true);
                }
                for (const auto subformula : subs.fals) {
                    reasons = combine_reasons(reasons, states[subformula].reasons_false);
                }

                // upwards propagation
                if (subs.multi.empty() && subs.confl.empty()) {
                    if (subs.tru.size() % 2 != 0) {
                        add_reasons_true(id, reasons);
                    } else {
                        add_reasons_false(id, reasons);
                    }
                }

                // downwards propagation
                if (downwards_propagation) {
                    if (subs.multi.size() == 1 && subs.confl.empty()) {
                        bool value = (subs.tru.size() % 2 != 0);
                        if (val == Valuation::TRUE) {
                            reasons = combine_reasons(reasons, states[id].reasons_true);
                            value = !value;
                        } else if (val == Valuation::FALSE) {
                            reasons = combine_reasons(reasons, states[id].reasons_false);
                        }

                        if (value) {
                            add_reasons_true(*subs.multi.begin(), reasons);
                        } else {
                            add_reasons_false(*subs.multi.begin(), reasons);
                        }
                    }
                }
            }
        },
        [&](BOOL&) {},
        [&](CONSTRAINT&) {},
    }, formula->db[id].content);

}

void FormulaTreeState::propagate_root(FormulaID id, bool is_true) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id << ", " << is_true);
    if (is_true) {
        states[id].reasons_true.emplace_back();
    } else {
        states[id].reasons_false.emplace_back();
    }
    propagate_consistency(id);
}

void FormulaTreeState::propagate_decision(FormulaID id, bool is_true) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id << ", " << is_true);
    FormulaState::Reasons reasons;
    reasons.emplace_back(FormulaState::Reason({std::make_pair(id, is_true)}));
    if (is_true) {
        add_reasons_true(id, reasons);
    } else {
        add_reasons_false(id, reasons);
    }
}

void FormulaTreeState::add_reasons_true(FormulaID id, const FormulaState::Reasons& reasons) {
    if (merge_reasons(states[id].reasons_true, reasons)) {
        if (valuation(id) != Valuation::UNKNOWN) {
            for (const auto parent : formula->db[id].parents) {
                propagate_consistency(parent);
            }
            propagate_consistency(id);
        } else {
            conflicts.insert(id);
        }
    }
}

void FormulaTreeState::add_reasons_false(FormulaID id, const FormulaState::Reasons& reasons) {
    if (merge_reasons(states[id].reasons_false, reasons)) {
        if (valuation(id) != Valuation::UNKNOWN) {
            for (const auto parent : formula->db[id].parents) {
                propagate_consistency(parent);
            }
            propagate_consistency(id);
        } else {
            conflicts.insert(id);
        }
    }
}    

FormulaState::Reasons FormulaTreeState::conflict_reasons() const {
    FormulaState::Reasons reasons;
    for (const auto c : conflicts) {
        merge_reasons(reasons,combine_reasons(states[c].reasons_false, states[c].reasons_true));            
    }
    return reasons;
}

void FormulaTreeState::backtrack(FormulaID id, bool is_true) {
    for (formula_ds::FormulaID idx = 0; idx < formula->db.size(); ++idx) {
        auto& f = states[idx];
        for (auto reason = f.reasons_true.begin(); reason != f.reasons_true.end(); ) {
            if (std::binary_search(reason->begin(), reason->end(), std::make_pair(id, is_true))) {
                reason = f.reasons_true.erase(reason);
            } else {
                reason++;
            }
        }
        for (auto reason = f.reasons_false.begin(); reason != f.reasons_false.end(); ) {
            if (std::binary_search(reason->begin(), reason->end(), std::make_pair(id, is_true))) {
                reason = f.reasons_false.erase(reason);
            } else {
                reason++;
            }
        }

        if (f.reasons_true.empty() || f.reasons_false.empty()) {
            conflicts.erase(idx);
        }
    }
}

}

inline carl::Variable new_var(const cadcells::Assignment& old_ass, const cadcells::Assignment& new_ass) {
    for (const auto& [k,v] : new_ass) {
        if (old_ass.find(k) == old_ass.end()) return k;
    }
    return carl::Variable::NO_VARIABLE;
}

namespace pp {

inline carl::BasicConstraint<Poly> normalize(const carl::BasicConstraint<Poly>& c) {
	assert(c.relation() == carl::Relation::LESS || c.relation() == carl::Relation::LEQ || c.relation() == carl::Relation::EQ || c.relation() == carl::Relation::NEQ);
	return carl::BasicConstraint<Poly>(c.lhs().normalize(), carl::is_negative(c.lhs().lcoeff()) ? carl::turn_around(c.relation()) : c.relation());
}

struct PolyInfo {
    bool EQ = false;
    bool NEQ = false;
    bool LESS = false;
    bool LEQ = false;
    bool GREATER = false;
    bool GEQ = false;
    void set(carl::Relation rel) {
        if (rel == carl::Relation::EQ) EQ = true;
        else if (rel == carl::Relation::NEQ) NEQ = true;
        else if (rel == carl::Relation::LESS) LESS = true;
        else if (rel == carl::Relation::LEQ) LEQ = true;
        else if (rel == carl::Relation::GREATER) GREATER = true;
        else if (rel == carl::Relation::GEQ) GEQ = true;
    }
};

FormulaT preprocess(const FormulaT& f) {
    std::vector<ConstraintT> constraints;
    carl::arithmetic_constraints(f, constraints);
    boost::container::flat_map<Poly,PolyInfo> info;
    for (const auto& c : constraints) {
        auto constr = normalize(c.constr());
        info.try_emplace(constr.lhs()).first->second.set(constr.relation());
    }

    std::vector<FormulaT> lemmas;
    for (const auto& [poly,rels] : info) {
        if ((rels.LESS || rels.GEQ) && (rels.GREATER || rels.LEQ)) {
            lemmas.emplace_back(carl::FormulaType::OR, FormulaT(ConstraintT(poly,carl::Relation::GEQ)), FormulaT(ConstraintT(poly,carl::Relation::LEQ)));
        }
        if ((rels.LESS || rels.GEQ) && (rels.EQ || rels.NEQ)) {
            lemmas.emplace_back(carl::FormulaType::OR, FormulaT(ConstraintT(poly,carl::Relation::NEQ)), FormulaT(ConstraintT(poly,carl::Relation::GEQ)));
        }
        if ((rels.GREATER || rels.LEQ) && (rels.EQ || rels.NEQ)) {
            lemmas.emplace_back(carl::FormulaType::OR, FormulaT(ConstraintT(poly,carl::Relation::NEQ)), FormulaT(ConstraintT(poly,carl::Relation::LEQ)));
        }
        if ((rels.LESS || rels.GEQ) && (rels.GREATER || rels.LEQ) && (rels.EQ || rels.NEQ)) {
            lemmas.emplace_back(carl::FormulaType::OR, FormulaT(ConstraintT(poly,carl::Relation::EQ)), FormulaT(ConstraintT(poly,carl::Relation::LESS)), FormulaT(ConstraintT(poly,carl::Relation::GREATER)));
        }
    }

    lemmas.push_back(f);
    return FormulaT(carl::FormulaType::AND, std::move(lemmas));
}

}


void GraphEvaluation::set_formula(const FormulaT& f) {
    auto input = f;
    if (m_preprocess) {
        input = pp::preprocess(input);
        SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Got " << input);
    }

    auto tree = std::make_shared<formula_ds::FormulaTree>(formula_ds::to_formula_tree(m_proj, input));
    true_graph.formula = tree;
    false_graph.formula = tree;
    true_graph.states.resize(tree->db.size());
    false_graph.states.resize(tree->db.size());
    true_graph.downwards_propagation = m_boolean_exploration != OFF;
    false_graph.downwards_propagation = m_boolean_exploration != OFF;

    for (auto& [var, atoms] : tree->vartof) {
        if (var.type() == carl::VariableType::VT_REAL) {
            std::sort(atoms.begin(), atoms.end(), [&](const formula_ds::FormulaID a, const formula_ds::FormulaID b) {
                const auto& constr_a = std::get<formula_ds::CONSTRAINT>(tree->db[a].content).constraint;
                const auto& constr_b = std::get<formula_ds::CONSTRAINT>(tree->db[b].content).constraint;
                return m_constraint_complexity_ordering(m_proj, constr_a, constr_b);
            });
        }
    }

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Initial formula:");
    log(tree->db, true_graph.states, tree->root);
    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Polynomials:" << m_proj.polys());

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update true_graph");
    for (formula_ds::FormulaID i = 0; i < true_graph.formula->db.size(); i++) {
        if (std::holds_alternative<formula_ds::TRUE>(true_graph.formula->db[i].content)) {
            true_graph.propagate_root(i, true);
        }
        if (std::holds_alternative<formula_ds::FALSE>(true_graph.formula->db[i].content)) {
            true_graph.propagate_root(i, false);
        }
    }
    true_graph.propagate_root(false_graph.formula->root, true);
    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update false_graph");
    for (formula_ds::FormulaID i = 0; i < true_graph.formula->db.size(); i++) {
        if (std::holds_alternative<formula_ds::TRUE>(false_graph.formula->db[i].content)) {
            false_graph.propagate_root(i, true);
        }
        if (std::holds_alternative<formula_ds::FALSE>(false_graph.formula->db[i].content)) {
            false_graph.propagate_root(i, false);
        }
    }
    false_graph.propagate_root(tree->root, false);
}

formula_ds::FormulaState::Reasons GraphEvaluation::explore(formula_ds::FormulaTreeState& graph) {
    // this is a quick and dirty implementation of a SAT solver
    std::optional<formula_ds::FormulaID> next_dec_id;
    for (const auto& [k,vs] : graph.formula->vartof) {
        if (m_boolean_exploration == EXPLORATION_ONLY_BOOL && k.type() != carl::VariableType::VT_BOOL) continue;
        for (const auto& v : vs) {
            if (graph.states[v].reasons_true.empty() && graph.states[v].reasons_false.empty()) {
                next_dec_id = v;
                break;
            }
        }
        if (next_dec_id) break;
    }
    if (!next_dec_id) return formula_ds::FormulaState::Reasons();

    graph.propagate_decision(*next_dec_id, true);
    auto true_conflicts = graph.conflict_reasons();
    if (true_conflicts.empty()) {
        true_conflicts = explore(graph);
    }
    graph.backtrack(*next_dec_id, true);
    if (true_conflicts.empty()) {
        return formula_ds::FormulaState::Reasons();   
    }

    graph.propagate_decision(*next_dec_id, false);
    auto false_conflicts = graph.conflict_reasons();
    if (false_conflicts.empty()) {
        false_conflicts = explore(graph);
    }
    graph.backtrack(*next_dec_id, false);
    if (false_conflicts.empty()) {
        return formula_ds::FormulaState::Reasons();   
    }

    formula_ds::FormulaState::Reasons conflicts;
    for (auto conflict : formula_ds::combine_reasons(true_conflicts, false_conflicts)) {
        std::erase(conflict, std::make_pair(*next_dec_id, true));
        std::erase(conflict, std::make_pair(*next_dec_id, false));
        formula_ds::merge_reason(conflicts, conflict);
    }
    return conflicts;
}

void GraphEvaluation::extend_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(assignment, ass);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
	if(root_valuation() != Valuation::MULTIVARIATE) return;
    auto atoms = true_graph.formula->vartof.find(var);
    if (atoms == true_graph.formula->vartof.end()) return;

    for (const auto id : atoms->second) {
        const auto& constr = std::get<formula_ds::CONSTRAINT>(true_graph.formula->db[id].content).constraint;
        assert (m_proj.main_var(constr.lhs) == var);

        SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Evaluate constraint " << constr);
        auto res = m_proj.evaluate(ass, constr);
        if (!boost::indeterminate(res)) {
            m_decisions.emplace(id, (bool)res);
            SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update true_graph");
            true_graph.propagate_decision(id, (bool)res);
            SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update false_graph");
            false_graph.propagate_decision(id, (bool)res);
        }

        if (m_stop_evaluation_on_conflict && (!true_graph.conflicts.empty() || !false_graph.conflicts.empty())) {
            break;
        }
    }

    if (!true_graph.conflicts.empty()) {
        assert(m_true_conflict_reasons.empty());
        m_true_conflict_reasons = true_graph.conflict_reasons();
    }
    if (!false_graph.conflicts.empty()) {
        assert(m_false_conflict_reasons.empty());
        m_false_conflict_reasons = false_graph.conflict_reasons();
    }

    if (m_boolean_exploration == EXPLORATION || m_boolean_exploration == EXPLORATION_ONLY_BOOL) {
        if (m_true_conflict_reasons.empty()) {
            m_true_conflict_reasons = explore(true_graph);
        }
        if (m_false_conflict_reasons.empty()) {
            m_false_conflict_reasons = explore(false_graph);
        }
        assert(m_true_conflict_reasons.empty() || m_false_conflict_reasons.empty());
    }
}

void GraphEvaluation::revert_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(ass, assignment);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
    auto atomset = true_graph.formula->vartof.find(var);
    if (atomset == true_graph.formula->vartof.end()) return;

    for (const auto id : atomset->second) {
        true_graph.backtrack(id, m_decisions[id]);
        false_graph.backtrack(id, m_decisions[id]);

        for (auto iter = m_true_conflict_reasons.begin(); iter != m_true_conflict_reasons.end(); ) {
            if (std::binary_search(iter->begin(), iter->end(), std::make_pair(id, m_decisions[id]))) {
                iter = m_true_conflict_reasons.erase(iter);
            } else {
                iter++;
            }
        }

        for (auto iter = m_false_conflict_reasons.begin(); iter != m_false_conflict_reasons.end(); ) {
            if (std::binary_search(iter->begin(), iter->end(), std::make_pair(id, m_decisions[id]))) {
                iter = m_false_conflict_reasons.erase(iter);
            } else {
                iter++;
            }
        }

        m_decisions.erase(id);
    }
}

void postprocess(cadcells::datastructures::Projections& proj, Implicant& i) {
    // Replace equations by their Gröbner basis if possible
    // TODO reduce other constraints using the gröbner basis?

    boost::container::flat_set<cadcells::Constraint> implicant;
    for (const auto& e : i) {
        implicant.insert(proj.polys()(e));
    }
    std::vector<cadcells::Polynomial> equations;
    for (const auto& c : implicant) {
        if (c.relation() == carl::Relation::EQ) {
            equations.emplace_back(c.lhs());
        }
    }
    if (equations.size()>1) {
        equations = carl::groebner_basis(equations);
        for (auto it = implicant.begin(); it != implicant.end(); ) {
            if (it->relation() == carl::Relation::EQ) {
                it = implicant.erase(it);
            } else {
                it++;
            }
        }
        for (const auto& poly : equations) {
            implicant.emplace(poly, carl::Relation::EQ);
        }
    }
    i.clear();
    for (const auto& e : implicant) {
        i.insert(proj.polys()(e));
    }
}

std::vector<Implicant> GraphEvaluation::compute_implicants() {
    auto reasons = (root_valuation() == Valuation::FALSE) ? m_true_conflict_reasons : m_false_conflict_reasons;

    std::vector<Implicant> implicants;
    for (const auto& r : reasons) {
        implicants.emplace_back();
        for (const auto& c : r) {
            if (c.second) {
                implicants.back().insert(std::get<formula_ds::CONSTRAINT>(true_graph.formula->db[c.first].content).constraint);
            } else {
                implicants.back().insert(m_proj.negation(std::get<formula_ds::CONSTRAINT>(true_graph.formula->db[c.first].content).constraint));
            }
        }
    }

    SMTRAT_STATISTICS_CALL(statistics().implicants_found(implicants.size()));

    // TODO pre-compute features and sort then?
    if (m_results == 1) {
        *implicants.begin() = *std::min_element(implicants.begin(), implicants.end(), std::bind_front(m_implicant_complexity_ordering, m_proj));
        implicants.erase(implicants.begin() + 1, implicants.end());
    } else if (m_results > 1) {
        std::sort(implicants.begin(), implicants.end(), std::bind_front(m_implicant_complexity_ordering, m_proj));
        if (m_results < implicants.size())
            implicants.erase(implicants.begin() + m_results, implicants.end());
    }

    if (m_postprocess) {
        for (auto& implicant : implicants) {
            postprocess(m_proj, implicant);
        }
    }

    return implicants;
}

Valuation GraphEvaluation::root_valuation() const {
    assert(m_true_conflict_reasons.empty() || m_false_conflict_reasons.empty());
    if (!m_true_conflict_reasons.empty()) return Valuation::FALSE;
    else if (!m_false_conflict_reasons.empty()) return Valuation::TRUE;
    else return Valuation::MULTIVARIATE;
}

}