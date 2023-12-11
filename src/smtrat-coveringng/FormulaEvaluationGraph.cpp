#include "FormulaEvaluationGraph.h"

#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/ran/Conversion.h>

#include <carl-common/util/streamingOperators.h>

namespace smtrat::covering_ng::formula {
using carl::operator<<;

namespace formula_ds {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

void print(std::ostream& stream, const FormulaDB& db, const FormulaID id, const std::size_t level) {
    std::visit(overloaded{
        [&](const TRUE&) {
            stream << std::string(level, ' ') << "TRUE";
        },
        [&](const FALSE&) {
            stream << std::string(level, ' ') << "FALSE";
        },
        [&](const NOT& c) {
            stream << std::string(level, ' ') << "NOT(" << std::endl;
            print(stream, db, c.subformula, level+1);
            stream << std::endl << std::string(level, ' ') << ")";
        },
        [&](const AND& c) {
            stream << std::string(level, ' ') << "AND(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const OR& c) {
            stream << std::string(level, ' ') << "OR(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const IFF& c) {
            stream << std::string(level, ' ') << "IFF(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const XOR& c) {
            stream << std::string(level, ' ') << "XOR(" << std::endl;
            for (const auto subformula : c.subformulas) {
                print(stream, db, subformula, level+1);
                stream << std::endl;
            }
            stream << std::string(level, ' ') << ")";
        },
        [&](const BOOL& c) {
            stream << std::string(level, ' ') << c.variable;
        },
        [&](const CONSTRAINT& c) {
            stream << std::string(level, ' ') << *c.constraint;
        },
    }, db[id].content);

    std::size_t spacing = 50 - level;
    if (level > 50) spacing = 4;

    stream << std::string(spacing, ' ') << "id: " << id << " T: " << db[id].reasons_true << " F: " << db[id].reasons_false;
}

void log(const FormulaDB& db, const FormulaID id) {
    std::stringstream ss;
    ss << std::endl;
    print(ss, db, id, 0);
    ss << std::endl;
    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", ss.str());
}


FormulaID to_formula_db(typename cadcells::Polynomial::ContextType c, const FormulaT& f,  FormulaDB& db, VariableToFormula& vartof, std::map<std::size_t,FormulaID>& cache) {
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
            auto bc = carl::convert<cadcells::Polynomial>(c, f.constraint().constr());
            db.emplace_back(CONSTRAINT{ std::make_shared<carl::BasicConstraint<cadcells::Polynomial>>(bc) });
            auto var = bc.lhs().main_var();
            vartof.try_emplace(var).first->second.insert((FormulaID)(db.size()-1));
            cache.emplace(f.id(), (FormulaID)(db.size()-1));
            return (FormulaID)(db.size()-1);
        }
        case carl::FormulaType::BOOL: {
            db.emplace_back(BOOL{ f.boolean() });
            vartof.try_emplace(f.boolean()).first->second.insert((FormulaID)(db.size()-1));
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

Formula::Reasons combine_reasons(const Formula::Reasons& a, const Formula::Reasons& b) {
    Formula::Reasons results;
    for (const auto& ar : a) {
        for (const auto& br : b) {
            auto tmp = ar;
            tmp.insert(br.begin(),br.end());
            results.insert(tmp);
        }
    }
    return results;
}

bool merge_reasons(Formula::Reasons& set, const Formula::Reasons& add) {
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

struct FormulaClassification {
    std::vector<FormulaID> tru;
    std::vector<FormulaID> fals;
    std::vector<FormulaID> multi;
    std::vector<FormulaID> confl;
};

FormulaClassification classify_formulas(const FormulaDB& db, const std::vector<FormulaID>& formulas) {
    FormulaClassification subs;
    for (const auto f : formulas) {
        auto sub_val = db[f].valuation();
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



void FormulaGraph::propagate_consistency(FormulaID id) {
    if (db[id].valuation() == Valuation::UNKNOWN) {
        return;
    }

    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id);
    #ifdef SMTRAT_DEVOPTION_Expensive
    log(db, root);
    #endif

    return std::visit(overloaded{
        [&](TRUE&) {},
        [&](FALSE&) {},
        [&](NOT& c) {
            auto val = db[id].valuation();
            auto sub_val = db[c.subformula].valuation();

            // upwards propagation
            if (sub_val == Valuation::TRUE) add_reasons_false(id, db[c.subformula].reasons_true);
            else if (sub_val == Valuation::FALSE) add_reasons_true(id, db[c.subformula].reasons_false);

            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE && sub_val == Valuation::MULTIVARIATE) { // sub_val == Valuation::MULTIVARIATE to avoid redundancies // TODO geht hierdurch was verloren?
                    add_reasons_false(c.subformula, db[id].reasons_true);
                } else if (val == Valuation::FALSE && sub_val == Valuation::MULTIVARIATE) {
                    add_reasons_true(c.subformula, db[id].reasons_false);
                }
            }
        },
        [&](AND& c) {
            auto val = db[id].valuation();
            auto subs = classify_formulas(db, c.subformulas);

            // upwards propagation
            {
                if (!subs.fals.empty()) {
                    for (const auto& subformula : subs.fals) {
                        add_reasons_false(id, db[subformula].reasons_false);
                    }
                } else if (subs.confl.empty() && subs.multi.empty() && subs.fals.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto& subformula : subs.tru) {
                        reasons = combine_reasons(reasons, db[subformula].reasons_true);
                    }
                    add_reasons_true(id, reasons);
                }
            }

            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    for (const auto subformula : subs.multi) { // avoids redundancy
                        add_reasons_true(subformula, db[id].reasons_true);
                    }
                } else if (val == Valuation::FALSE) {
                    if (subs.multi.size() == 1 && subs.confl.empty() && subs.fals.empty()) {
                        Formula::Reasons reasons = db[id].reasons_false;
                        for (const auto& subformula : subs.tru) {
                            reasons = combine_reasons(reasons, db[subformula].reasons_true);
                        }
                        add_reasons_false(*subs.multi.begin(), reasons);
                    }
                }
            }
        },
        [&](OR& c) {
            auto val = db[id].valuation();
            auto subs = classify_formulas(db, c.subformulas);

            // upwards propagation
            {
                if (!subs.tru.empty()) {
                    for (const auto& subformula : subs.tru) {
                        add_reasons_true(id, db[subformula].reasons_true);
                    }
                } else if (subs.confl.empty() && subs.multi.empty() && subs.tru.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto& subformula : subs.fals) {
                        reasons = combine_reasons(reasons, db[subformula].reasons_false);
                    }
                    add_reasons_false(id, reasons);
                }
            } 
            
            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    if (subs.multi.size() == 1 && subs.confl.empty() && subs.tru.empty()) {
                        Formula::Reasons reasons = db[id].reasons_true;
                        for (const auto& subformula : subs.fals) {
                            reasons = combine_reasons(reasons, db[subformula].reasons_false);
                        }
                        add_reasons_true(*subs.multi.begin(), reasons);
                    }
                } else if (val == Valuation::FALSE) {
                    for (const auto subformula : subs.multi) { // avoids redundancy
                        add_reasons_false(subformula, db[id].reasons_false);
                    }
                }
            }
        },
        [&](IFF& c) {
            auto subs = classify_formulas(db, c.subformulas);
            auto val = db[id].valuation();

            // upwards propagation
            {
                if (!subs.tru.empty() && !subs.fals.empty()) {
                    Formula::Reasons reasons;
                    for (const auto t : subs.tru) {
                        for (const auto f : subs.fals) {
                            auto tmp = combine_reasons(db[t].reasons_true,db[f].reasons_false);
                            reasons.insert(tmp.begin(), tmp.end());
                        }
                    }
                    add_reasons_false(id, reasons);
                } else if (subs.multi.empty() && !subs.tru.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto t : subs.tru) {
                        reasons = combine_reasons(reasons, db[t].reasons_true);
                    }
                    add_reasons_true(id, reasons);
                } else if (subs.multi.empty() && !subs.fals.empty()) {
                    Formula::Reasons reasons;
                    reasons.emplace();
                    for (const auto f : subs.fals) {
                        reasons = combine_reasons(reasons, db[f].reasons_false);
                    }
                    add_reasons_true(id, reasons);
                } 
            }
            
            // downwards propagation
            if (downwards_propagation) {
                if (val == Valuation::TRUE) {
                    for (const auto t : subs.tru) {
                        for (const auto sub : c.subformulas) {
                            auto sub_val = db[sub].valuation();
                            if (sub_val == Valuation::MULTIVARIATE) { // avoids redundancy
                                add_reasons_true(sub, combine_reasons(db[id].reasons_true, db[t].reasons_true));
                            }
                        }
                    }
                    for (const auto f : subs.fals) {
                        for (const auto sub : c.subformulas) {
                            auto sub_val = db[sub].valuation();
                            if (sub_val == Valuation::MULTIVARIATE) { // avoids redundancy
                                add_reasons_false(sub, combine_reasons(db[id].reasons_true, db[f].reasons_false));
                            }
                        }
                    }
                } else if (val == Valuation::FALSE) {
                    if (subs.multi.size() == 1 && (subs.tru.empty() || subs.fals.empty())) {
                        if (subs.tru.empty()) {
                            Formula::Reasons reasons = db[id].reasons_false;
                            for (const auto f : subs.fals) {
                                reasons = combine_reasons(reasons, db[f].reasons_false);
                            }
                            add_reasons_true(*subs.multi.begin(), reasons);
                        } else {
                            assert(subs.fals.empty());
                            Formula::Reasons reasons = db[id].reasons_false;
                            for (const auto t : subs.tru) {
                                reasons = combine_reasons(reasons, db[t].reasons_true);
                            }
                            add_reasons_false(*subs.multi.begin(), reasons);
                        }
                    }
                }
            }
        },
        [&](XOR& c) {
            auto val = db[id].valuation();
            auto subs = classify_formulas(db, c.subformulas);

            if (subs.confl.empty() && (subs.multi.empty() || subs.multi.size() == 1)) {
                Formula::Reasons reasons;
                reasons.emplace();
                for (const auto subformula : subs.tru) {
                    reasons = combine_reasons(reasons, db[subformula].reasons_true);
                }
                for (const auto subformula : subs.fals) {
                    reasons = combine_reasons(reasons, db[subformula].reasons_false);
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
                            reasons = combine_reasons(reasons, db[id].reasons_true);
                            value = !value;
                        } else if (val == Valuation::FALSE) {
                            reasons = combine_reasons(reasons, db[id].reasons_false);
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
    }, db[id].content);

}

void FormulaGraph::propagate_root(FormulaID id, bool is_true) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id << ", " << is_true);
    if (is_true) {
        db[id].reasons_true.emplace();
    } else {
        db[id].reasons_false.emplace();
    }
    propagate_consistency(id);
}

void FormulaGraph::propagate_decision(FormulaID id, bool is_true) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id << ", " << is_true);
    Formula::Reasons reasons;
    reasons.insert(Formula::Reason({std::make_pair(id, is_true)}));
    if (is_true) {
        add_reasons_true(id, reasons);
    } else {
        add_reasons_false(id, reasons);
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

void FormulaGraph::backtrack(FormulaID id, bool is_true) {
    for (formula_ds::FormulaID idx = 0; idx < db.size(); ++idx) {
        auto& f = db[idx];
        for (auto reason = f.reasons_true.begin(); reason != f.reasons_true.end(); ) {
            if (reason->find(std::make_pair(id, is_true)) != reason->end()) {
                f.reasons_true.erase(reason);
            } else {
                reason++;
            }
        }
        for (auto reason = f.reasons_false.begin(); reason != f.reasons_false.end(); ) {
            if (reason->find(std::make_pair(id, is_true)) != reason->end()) {
                f.reasons_false.erase(reason);
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

carl::Variable new_var(const cadcells::Assignment& old_ass, const cadcells::Assignment& new_ass) {
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


void GraphEvaluation::set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    auto input = f;
    if (m_preprocess) {
        input = pp::preprocess(input);
        SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Got " << input);
    }
    
    std::map<std::size_t,formula_ds::FormulaID> cache;
    true_graph.root = to_formula_db(c, input, true_graph.db, vartof, cache);
    true_graph.downwards_propagation = m_boolean_exploration != OFF;
    false_graph = true_graph;

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Initial formula:");
    log(true_graph.db, true_graph.root);

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update true_graph");
    for (formula_ds::FormulaID i = 0; i < true_graph.db.size(); i++) {
        if (std::holds_alternative<formula_ds::TRUE>(true_graph.db[i].content)) {
            true_graph.propagate_root(i, true);
        }
        if (std::holds_alternative<formula_ds::FALSE>(true_graph.db[i].content)) {
            true_graph.propagate_root(i, false);
        }
    }
    true_graph.propagate_root(true_graph.root, true);
    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update false_graph");
    for (formula_ds::FormulaID i = 0; i < false_graph.db.size(); i++) {
        if (std::holds_alternative<formula_ds::TRUE>(false_graph.db[i].content)) {
            false_graph.propagate_root(i, true);
        }
        if (std::holds_alternative<formula_ds::FALSE>(false_graph.db[i].content)) {
            false_graph.propagate_root(i, false);
        }
    }
    false_graph.propagate_root(false_graph.root, false);
}

formula_ds::Formula::Reasons GraphEvaluation::explore(formula_ds::FormulaGraph& graph) {
    // this is a quick and dirty implementation of a SAT solver
    std::optional<formula_ds::FormulaID> next_dec_id;
    for (const auto& [k,vs] : vartof) {
        if (m_boolean_exploration == EXPLORATION_ONLY_BOOL && k.type() != carl::VariableType::VT_BOOL) continue;
        for (const auto& v : vs) {
            if (graph.db[v].reasons_true.empty() && graph.db[v].reasons_false.empty()) {
                next_dec_id = v;
                break;
            }
        }
        if (next_dec_id) break;
    }
    if (!next_dec_id) return formula_ds::Formula::Reasons();

    graph.propagate_decision(*next_dec_id, true);
    auto true_conflicts = graph.conflict_reasons();
    if (true_conflicts.empty()) {
        true_conflicts = explore(graph);
    }
    graph.backtrack(*next_dec_id, true);
    if (true_conflicts.empty()) {
        return formula_ds::Formula::Reasons();   
    }

    graph.propagate_decision(*next_dec_id, false);
    auto false_conflicts = graph.conflict_reasons();
    if (false_conflicts.empty()) {
        false_conflicts = explore(graph);
    }
    graph.backtrack(*next_dec_id, false);
    if (false_conflicts.empty()) {
        return formula_ds::Formula::Reasons();   
    }

    formula_ds::Formula::Reasons conflicts;
    for (auto conflict : formula_ds::combine_reasons(true_conflicts, false_conflicts)) {
        conflict.erase(std::make_pair(*next_dec_id, true));
        conflict.erase(std::make_pair(*next_dec_id, false));
        conflicts.insert(conflict);
    }
    return conflicts;
}

void GraphEvaluation::extend_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(assignment, ass);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
	if(root_valuation() != Valuation::MULTIVARIATE) return;
    auto atomset = vartof.find(var);
    if (atomset == vartof.end()) return;

    std::vector<formula_ds::FormulaID> atoms(atomset->second.begin(), atomset->second.end());
    std::sort(atoms.begin(), atoms.end(), [&](const formula_ds::FormulaID a, const formula_ds::FormulaID b) {
        const auto& constr_a = *std::get<formula_ds::CONSTRAINT>(true_graph.db[a].content).constraint;
        const auto& constr_b = *std::get<formula_ds::CONSTRAINT>(true_graph.db[b].content).constraint;
        return m_constraint_complexity_ordering(constr_a, constr_b);
    });

    for (const auto id : atoms) {
        const auto& constr = *std::get<formula_ds::CONSTRAINT>(true_graph.db[id].content).constraint;
        assert (constr.lhs().main_var() == var);

        SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Evaluate constraint " << constr);
        auto res = carl::evaluate(constr, ass);
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

    // TODO gröbner propagation
}

void GraphEvaluation::revert_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(ass, assignment);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
    auto atomset = vartof.find(var);
    if (atomset == vartof.end()) return;

    for (const auto id : atomset->second) {
        true_graph.backtrack(id, m_decisions[id]);
        false_graph.backtrack(id, m_decisions[id]);

        for (auto iter = m_true_conflict_reasons.begin(); iter != m_true_conflict_reasons.end(); ) {
            if (iter->find(std::make_pair(id, m_decisions[id])) != iter->end()) {
                iter = m_true_conflict_reasons.erase(iter);
            } else {
                iter++;
            }
        }

        for (auto iter = m_false_conflict_reasons.begin(); iter != m_false_conflict_reasons.end(); ) {
            if (iter->find(std::make_pair(id, m_decisions[id])) != iter->end()) {
                iter = m_false_conflict_reasons.erase(iter);
            } else {
                iter++;
            }
        }

        m_decisions.erase(id);
    }
}

void postprocess(boost::container::flat_set<cadcells::Constraint>& implicant) {
    // Replace equations by their Gröbner basis if possible
    // TODO reduce other constraints using the gröbner basis?
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
}

std::vector<boost::container::flat_set<cadcells::Constraint>> GraphEvaluation::compute_implicants() const {
    auto reasons = (root_valuation() == Valuation::FALSE) ? m_true_conflict_reasons : m_false_conflict_reasons;

    std::vector<boost::container::flat_set<cadcells::Constraint>> implicants;
    for (const auto& r : reasons) {
        implicants.emplace_back();
        for (const auto& c : r) {
            if (c.second) {
                implicants.back().insert(*std::get<formula_ds::CONSTRAINT>(true_graph.db[c.first].content).constraint);
            } else {
                implicants.back().insert(std::get<formula_ds::CONSTRAINT>(true_graph.db[c.first].content).constraint->negation());
            }
        }
    }

    if (m_results != 0) {
        std::sort(implicants.begin(), implicants.end(), m_implicant_complexity_ordering);
        if (m_results < implicants.size())
            implicants.erase(implicants.begin() + m_results, implicants.end());
    }

    if (m_postprocess) {
        for (auto& implicant : implicants) {
            postprocess(implicant);
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