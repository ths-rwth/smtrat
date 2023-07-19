#include "FormulaEvaluationGraph.h"

#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/ran/Conversion.h>

namespace smtrat::covering_ng::formula {

namespace formula_ds {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


FormulaID to_formula_db(typename cadcells::Polynomial::ContextType c, const FormulaT& f,  FormulaDB& db, VariableToFormula& vartof, std::map<std::size_t,FormulaID>& cache) {

    {
        auto cache_it = cache.find(f.id());
        if (cache_it != cache.end()) return cache_it->second;
    }
    switch(f.type()) {
        case carl::FormulaType::ITE: {
            return to_formula_db(c, FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, f.condition(), f.first_case()), FormulaT(carl::FormulaType::AND, f.condition().negated(), f.second_case())), db, vartof, cache);
        }
        case carl::FormulaType::TRUE: {
            db.emplace_back(db.size()-1, TRUE{ });
            return db.size()-1;
        }
        case carl::FormulaType::FALSE: {
            db.emplace_back(db.size()-1, FALSE{ });
            return db.size()-1;
        }
        case carl::FormulaType::BOOL: {
            db.emplace_back(db.size()-1, BOOL{ f.boolean() });
            vartof.try_emplace(f.boolean()).first->second.insert(db.size()-1);
            return db.size()-1;
        }
        case carl::FormulaType::NOT: {
            auto child = to_formula_db(c,f.subformula(),db,vartof, cache);
            db.emplace_back(db.size()-1, NOT{ child });
            db[child].parents.insert(db.size()-1);
            return db.size()-1;
        }
        case carl::FormulaType::IMPLIES: {
            return to_formula_db(c, FormulaT(carl::FormulaType::OR, f.premise().negated(), f.conclusion()), db, vartof, cache);
        }
        case carl::FormulaType::AND: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(db.size()-1, AND{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert(db.size()-1);
            }
            return db.size()-1;
        }
        case carl::FormulaType::OR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(db.size()-1, OR{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert(db.size()-1);
            }
            return db.size()-1;
        }
        case carl::FormulaType::XOR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(db.size()-1, XOR{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert(db.size()-1);
            }
            return db.size()-1;
        }
        case carl::FormulaType::IFF: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(db.size()-1, IFF{ subformulas });
            for (const auto child : subformulas) {
                db[child].parents.insert(db.size()-1);
            }
            return db.size()-1;
        }
        case carl::FormulaType::CONSTRAINT: {
            auto bc = carl::convert<cadcells::Polynomial>(c, f.constraint().constr());
            db.emplace_back(db.size()-1, CONSTRAINT{ bc });
            for (const auto var : f.constraint().variables()) {
                vartof.try_emplace(var).first->second.insert(db.size()-1);
            }
            return db.size()-1;
        }
        default: {
            assert(false);
            db.emplace_back(db.size()-1, FALSE{});
            return db.size()-1;
        }
    }
}

Formula::Reasons combine_reasons(const Formula::Reasons& a, const Formula::Reasons& b) {
    Formula::Reasons results;
    for (const auto& ar : a) {
        for (const auto& br : b) {
            boost::container::flat_set<FormulaID> tmp = ar;
            tmp.insert(br.begin(),br.end());
            results.insert(tmp);
        }
    }
    return results;
}

bool merge_reasons(boost::container::flat_set<boost::container::flat_set<FormulaID>>& set, const boost::container::flat_set<boost::container::flat_set<FormulaID>>& add) {
    bool change = false;
    for (const auto& a : add) {
        // if there is a set that is a subset of the set to be added, we can stop
        if (std::find_if(set.begin(), set.end(), [&](const auto& s) {
            return std::includes(a.begin(), a.end(), s.begin(), s.end());
        }) != set.end()) continue;

        // we remove all sets that contain the set to be added
        for (auto s = set.begin(); s != set.end(); ) {
            if (std::includes(s->begin(), s->end(), a.begin(), a.end())) {
                set.erase(s);
            } else {
                s++;
            }
        }

        set.insert(a); // finally, we add the set
        change = true;
    }
    return change;
}

void FormulaGraph::propagate_consistency(FormulaID id) {
    return std::visit(overloaded{
        [&](TRUE&) {},
        [&](FALSE&) {},
        [&](NOT& c) {
            auto val = db[id].valuation();
            auto sub_val = db[c.subformula].valuation();
            if (val != Valuation::MULTIVARIATE && sub_val == Valuation::MULTIVARIATE) {
                if (val == Valuation::TRUE) add_reasons_false(c.subformula, db[id].reasons_true);
                else if (val == Valuation::FALSE) add_reasons_true(c.subformula, db[id].reasons_false);
                else assert(false);
            } else if (val == Valuation::MULTIVARIATE && sub_val != Valuation::MULTIVARIATE) {
                if (sub_val == Valuation::TRUE) add_reasons_false(id, db[c.subformula].reasons_true);
                else if (sub_val == Valuation::FALSE) add_reasons_true(id, db[c.subformula].reasons_false);
                else assert(false);
            } else {
                assert((val == Valuation::TRUE && sub_val == Valuation::FALSE) || (val == Valuation::FALSE && sub_val == Valuation::TRUE));
            }
        },
        [&](AND& c) {
            auto val = db[id].valuation();
            if (val == Valuation::MULTIVARIATE) {
                Formula::Reasons reasons_true;
                reasons_true.emplace();
                for (const auto subformula : c.subformulas) {
                    auto sub_val = db[subformula].valuation();
                    if (sub_val == Valuation::FALSE) {
                        add_reasons_false(id, db[subformula].reasons_false);
                        reasons_true.clear();
                    } else if (sub_val == Valuation::TRUE) {
                        reasons_true = combine_reasons(reasons_true, db[subformula].reasons_true);
                    } else if (sub_val == Valuation::MULTIVARIATE) {
                        reasons_true.clear();
                    } else {
                        assert(sub_val == Valuation::UNKNOWN);
                        reasons_true.clear();
                    }
                }
                if (!reasons_true.empty()) {
                    add_reasons_true(id, reasons_true);
                }
            } else if (val == Valuation::TRUE) {
                for (const auto subformula : c.subformulas) {
                    add_reasons_true(subformula, db[id].reasons_true);
                }
            } else if (val == Valuation::FALSE) {
                Formula::Reasons reasons_false;
                std::optional<FormulaID> implied_false;
                reasons_false = db[id].reasons_false;
                for (const auto subformula : c.subformulas) {
                    auto sub_val = db[subformula].valuation();
                    if (sub_val == Valuation::FALSE) {
                        reasons_false.clear();
                        implied_false = std::nullopt;
                    } else if (sub_val == Valuation::TRUE) {
                        reasons_false = combine_reasons(reasons_false, db[subformula].reasons_true);
                    } else if (sub_val == Valuation::MULTIVARIATE) {
                        if (!implied_false) {
                            implied_false = subformula;
                        } else {
                            reasons_false.clear();
                            implied_false = std::nullopt;
                        }
                    } else {
                        assert(sub_val == Valuation::UNKNOWN);
                        reasons_false.clear();
                        implied_false = std::nullopt;
                    }
                }
                if (implied_false) {
                    add_reasons_false(*implied_false, reasons_false);
                }
            } else assert(false);
        },
        [&](OR& c) {
            auto val = db[id].valuation();
            if (val == Valuation::MULTIVARIATE) {
                Formula::Reasons reasons_false;
                reasons_false.emplace();
                for (const auto subformula : c.subformulas) {
                    auto sub_val = db[subformula].valuation();
                    if (sub_val == Valuation::FALSE) {
                        reasons_false = combine_reasons(reasons_false, db[subformula].reasons_false);
                    } else if (sub_val == Valuation::TRUE) {
                        add_reasons_true(id, db[subformula].reasons_true);
                        reasons_false.clear();
                    } else if (sub_val == Valuation::MULTIVARIATE) {
                        reasons_false.clear();
                    } else {
                        assert(sub_val == Valuation::UNKNOWN);
                        reasons_false.clear();
                    }
                }
                if (!reasons_false.empty()) {
                    add_reasons_false(id, reasons_false);
                }
            } else if (val == Valuation::TRUE) {
                Formula::Reasons reasons_true;
                std::optional<FormulaID> implied_true;
                reasons_true = db[id].reasons_true;
                for (const auto subformula : c.subformulas) {
                    auto sub_val = db[subformula].valuation();
                    if (sub_val == Valuation::FALSE) {
                        reasons_true = combine_reasons(reasons_true, db[subformula].reasons_false);
                    } else if (sub_val == Valuation::TRUE) {
                        reasons_true.clear();
                        implied_true = std::nullopt;
                    } else if (sub_val == Valuation::MULTIVARIATE) {
                        if (!implied_true) {
                            implied_true = subformula;
                        } else {
                            reasons_true.clear();
                            implied_true = std::nullopt;
                        }
                    } else {
                        assert(sub_val == Valuation::UNKNOWN);
                        reasons_true.clear();
                        implied_true = std::nullopt;
                    }
                }
                if (implied_true) {
                    add_reasons_true(*implied_true, reasons_true);
                }
            } else if (val == Valuation::FALSE) {
                for (const auto subformula : c.subformulas) {
                    add_reasons_false(subformula, db[id].reasons_false);
                }
            } else assert(false);
        },
        [&](IFF& c) {
            std::vector<FormulaID> true_sub;
            std::vector<FormulaID> false_sub;
            std::vector<FormulaID> multivariate_sub;
            for (const auto subformula : c.subformulas) {
                auto sub_val = db[subformula].valuation();
                if (sub_val == Valuation::FALSE) {
                    false_sub.push_back(subformula);
                } else if (sub_val == Valuation::TRUE) {
                    true_sub.push_back(subformula);
                } else if (sub_val == Valuation::MULTIVARIATE) {
                    multivariate_sub.push_back(subformula);
                } else {
                    assert(sub_val == Valuation::UNKNOWN);
                    return;
                }
            }

            auto val = db[id].valuation();
            if (val == Valuation::MULTIVARIATE) {
                if (multivariate_sub.empty() && !true_sub.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto t : true_sub) {
                        reasons = combine_reasons(reasons, db[t].reasons_true);
                    }
                    add_reasons_true(id, reasons);
                } else if (multivariate_sub.empty() && !false_sub.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto f : false_sub) {
                        reasons = combine_reasons(reasons, db[f].reasons_false);
                    }
                    add_reasons_true(id, reasons);
                } else if (!true_sub.empty() && !false_sub.empty()) {
                    Formula::Reasons reasons;
                    for (const auto t : true_sub) {
                        for (const auto f : false_sub) {
                            auto tmp = combine_reasons(db[t].reasons_true,db[f].reasons_false);
                            reasons.insert(tmp.begin(), tmp.end());
                        }
                    }
                    add_reasons_false(id, reasons);
                }
            } else if (val == Valuation::TRUE) {
                for (const auto t : true_sub) {
                    for (const auto sub : c.subformulas) {
                        add_reasons_true(sub, combine_reasons(db[id].reasons_true, db[t].reasons_true));
                    }
                }
                for (const auto f : false_sub) {
                    for (const auto sub : c.subformulas) {
                        add_reasons_false(sub, combine_reasons(db[id].reasons_true, db[f].reasons_false));
                    }
                }
            } else if (val == Valuation::FALSE) {
                if (multivariate_sub.size() == 1 && (true_sub.empty() || false_sub.empty())) {
                    if (true_sub.empty()) {
                        Formula::Reasons reasons = db[id].reasons_false;
                        for (const auto f : false_sub) {
                            reasons = combine_reasons(reasons, db[f].reasons_false);
                        }
                        add_reasons_true(*multivariate_sub.begin(), reasons);
                    } else {
                        assert(false_sub.empty());
                        Formula::Reasons reasons = db[id].reasons_false;
                        for (const auto t : true_sub) {
                            reasons = combine_reasons(reasons, db[t].reasons_true);
                        }
                        add_reasons_false(*multivariate_sub.begin(), reasons);
                    }
                }
            } else assert(false);
        },
        [&](XOR& c) {
            std::optional<FormulaID> implied;
            Formula::Reasons reasons;
            bool value;

            auto val = db[id].valuation();
            if (val == Valuation::MULTIVARIATE) {
                implied = id;
                value = true;
                reasons.emplace();
            } else if (val == Valuation::TRUE) {
                value = false;
                reasons = db[id].reasons_true;
            } else if (val == Valuation::FALSE) {
                value = true;
                reasons = db[id].reasons_false;
            } else assert(false);

            for (const auto subformula : c.subformulas) {
                auto sub_val = db[subformula].valuation();
                if (sub_val == Valuation::MULTIVARIATE) {
                    if (implied) {
                        implied = id;
                    } else {
                        implied = std::nullopt;
                        reasons.clear();
                    }
                } else if (sub_val == Valuation::FALSE) {
                    reasons = combine_reasons(reasons, db[subformula].reasons_false);
                } else if (sub_val == Valuation::TRUE) {
                    reasons = combine_reasons(reasons, db[subformula].reasons_true);
                    value = !value;
                } else {
                    assert(sub_val == Valuation::UNKNOWN);
                    implied = std::nullopt;
                        reasons.clear();
                }
            }

            if (implied) {
                if (value) {
                    add_reasons_true(*implied, reasons);
                } else {
                    add_reasons_false(*implied, reasons);
                }
            }
        },
        [&](BOOL&) {},
        [&](CONSTRAINT&) {},
    }, db[id].content);

}

void FormulaGraph::propagate_root(FormulaID id, bool is_true) {
    if (is_true) {
        db[id].reasons_true.emplace();
    } else {
        db[id].reasons_false.emplace();
    }
    propagate_consistency(id);
}

void FormulaGraph::evaluate(FormulaID id, const cadcells::Assignment& ass, carl::Variable main_var) {
    assert(std::holds_alternative<CONSTRAINT>(db[id].content));
    const auto& constr = std::get<CONSTRAINT>(db[id].content).constraint;
    if (constr.lhs().main_var() != main_var) return;
    auto res = carl::evaluate(constr, ass);
    if (!boost::indeterminate(res)) {
        boost::container::flat_set<boost::container::flat_set<FormulaID>> reasons;
        reasons.insert(boost::container::flat_set<FormulaID>({id}));
        if (res) {
            add_reasons_true(id, reasons);
        } else {
            add_reasons_false(id, reasons);
        }
    }
}

void FormulaGraph::add_reasons_true(FormulaID id, const Formula::Reasons& reasons) {
    if (merge_reasons(db[id].reasons_true, reasons)) {
        if (db[id].valuation() != Valuation::UNKNOWN) {
            for (const auto parent : db[id].parents) {
                propagate_consistency(parent);
            }
            propagate_consistency(id);
        } else {
            conflicts.insert(id);
        }
    }
}

void FormulaGraph::add_reasons_false(FormulaID id, const Formula::Reasons& reasons) {
    if (merge_reasons(db[id].reasons_false, reasons)) {
        if (db[id].valuation() != Valuation::UNKNOWN) {
            for (const auto parent : db[id].parents) {
                propagate_consistency(parent);
            }
            propagate_consistency(id);
        } else {
            conflicts.insert(id);
        }
    }
}    

Formula::Reasons FormulaGraph::conflict_reasons() const {
    Formula::Reasons reasons;
    for (const auto c : conflicts) {
        reasons.merge(combine_reasons(db[c].reasons_false, db[c].reasons_true));            
    }
    return reasons;
}

void FormulaGraph::backtrack(FormulaID id) {
    for (auto& f : db) {
        for (auto reason = f.reasons_true.begin(); reason != f.reasons_true.end(); ) {
            if (reason->find(id) != reason->end()) {
                f.reasons_true.erase(reason);
            } else {
                reason++;
            }
        }
        for (auto reason = f.reasons_false.begin(); reason != f.reasons_false.end(); ) {
            if (reason->find(id) != reason->end()) {
                f.reasons_false.erase(reason);
            } else {
                reason++;
            }
        }

        if (f.reasons_true.empty() || f.reasons_false.empty()) {
            conflicts.erase(f.id);
        }
    }
}

}

carl::Variable new_var(const cadcells::Assignment& old_ass, const cadcells::Assignment& new_ass) {
    for (const auto& [k,v] : new_ass) {
        if (old_ass.find(k) == old_ass.end()) return k;
    }
    return carl::Variable::NO_VARIABLE;
}


void GraphEvaluation::set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    {std::map<std::size_t,formula_ds::FormulaID> cache;
    true_graph.root = to_formula_db(c, f, true_graph.db, true_graph.vartof, cache);
    true_graph.propagate_root(true_graph.root, true);}

    {std::map<std::size_t,formula_ds::FormulaID> cache;
    false_graph.root = to_formula_db(c, f, false_graph.db, false_graph.vartof, cache);
    false_graph.propagate_root(false_graph.root, false);}
}

void GraphEvaluation::extend_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(assignment, ass);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;

    for (const auto id : true_graph.vartof.find(var)->second) {
        true_graph.evaluate(id,ass,var);
    }

    for (const auto id : false_graph.vartof.find(var)->second) {
        false_graph.evaluate(id,ass,var);
    }
}

void GraphEvaluation::revert_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(ass, assignment);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;

    for (const auto id : true_graph.vartof.find(var)->second) {
        true_graph.backtrack(id);
    }

    for (const auto id : false_graph.vartof.find(var)->second) {
        false_graph.backtrack(id);
    }
}

std::vector<boost::container::flat_set<cadcells::Constraint>> GraphEvaluation::compute_implicants() const {
    auto reasons = (root_valuation() == Valuation::FALSE) ? true_graph.conflict_reasons() : false_graph.conflict_reasons();
    auto& graph = (root_valuation() == Valuation::FALSE) ? true_graph : false_graph;

    std::vector<boost::container::flat_set<cadcells::Constraint>> implicants;
    for (const auto& r : reasons) {
        implicants.emplace_back();
        for (const auto& c : r) {
            implicants.back().insert(std::get<formula_ds::CONSTRAINT>(graph.db[c].content).constraint);
        }
    }

    if (m_results != 0) {
        std::sort(implicants.begin(), implicants.end(), m_implicant_complexity_ordering);
        if (m_results < implicants.size())
            implicants.erase(implicants.begin() + m_results, implicants.end());
    }
    return implicants;
}

Valuation GraphEvaluation::root_valuation() const {
    assert(true_graph.conflicts.empty() || false_graph.conflicts.empty());
    if (!true_graph.conflicts.empty()) return Valuation::FALSE;
    else if (!false_graph.conflicts.empty()) return Valuation::TRUE;
    else return Valuation::MULTIVARIATE;
}

}