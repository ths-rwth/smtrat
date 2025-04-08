#include "FormulaEvaluationNoop.h"

#include <carl-arith/constraint/Conversion.h>
#include <carl-arith/ran/Conversion.h>

#include <carl-common/util/streamingOperators.h>

#include "CoveringNGStatistics.h"

namespace smtrat::covering_ng::formula {
using carl::operator<<;

namespace formula_noop_ds {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


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
    std::map<std::size_t,formula_noop_ds::FormulaID> cache;
    tree.root = to_formula_db(c, f, tree.db, tree.vartof, cache);
    return tree;
}

struct FormulaClassification {
    std::vector<FormulaID> tru;
    std::vector<FormulaID> fals;
    std::vector<FormulaID> multi;
};

inline FormulaClassification classify_formulas(const FormulaTree& ts, const std::vector<FormulaID>& formulas) {
    FormulaClassification subs;
    for (const auto f : formulas) {
        auto sub_val = ts.db.at(f).value;
        if (sub_val == Valuation::FALSE) {
            subs.fals.push_back(f);
        } else if (sub_val == Valuation::TRUE) {
            subs.tru.push_back(f);
        } else if (sub_val == Valuation::MULTIVARIATE) {
            subs.multi.push_back(f);
        } else {
            assert(sub_val == Valuation::UNKNOWN);
            assert(false);
        }
    }
    return subs;
}

void FormulaTree::propagate_consistency(FormulaID id) {
    SMTRAT_LOG_FUNC("smtrat.covering_ng.evaluation", id);

    auto old_value = db[id].value;

    std::visit(overloaded{
        [&](TRUE&) {
            db[id].value = Valuation::TRUE;
        },
        [&](FALSE&) {
            db[id].value = Valuation::FALSE;
        },
        [&](NOT& c) {
            auto sub_val = db.at(c.subformula).value;

            // upwards propagation
            if (sub_val == Valuation::TRUE) db[id].value = Valuation::FALSE;
            else if (sub_val == Valuation::FALSE) db[id].value = Valuation::TRUE;
            else db[id].value = Valuation::MULTIVARIATE;
        },
        [&](AND& c) {
            auto subs = classify_formulas(*this, c.subformulas);

            // upwards propagation
            {
                if (!subs.fals.empty()) {
                    db[id].value = Valuation::FALSE;
                } else if (subs.multi.empty() && subs.fals.empty()) {
                    db[id].value = Valuation::TRUE;
                } else {
                    db[id].value = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](OR& c) {
            auto subs = classify_formulas(*this, c.subformulas);

            // upwards propagation
            {
                if (!subs.tru.empty()) {
                    db[id].value = Valuation::TRUE;
                } else if (subs.multi.empty() && subs.tru.empty()) {
                    db[id].value = Valuation::FALSE;
                } else {
                    db[id].value = Valuation::MULTIVARIATE;
                }
            } 
        },
        [&](IFF& c) {
            auto subs = classify_formulas(*this, c.subformulas);

            // upwards propagation
            {
                if (!subs.tru.empty() && !subs.fals.empty()) {
                    db[id].value = Valuation::FALSE;
                } else if (subs.multi.empty() && !subs.tru.empty()) {
                    db[id].value = Valuation::TRUE;
                } else if (subs.multi.empty() && !subs.fals.empty()) {
                    db[id].value = Valuation::TRUE;
                } else {
                    db[id].value = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](XOR& c) {
            auto subs = classify_formulas(*this, c.subformulas);

            if (subs.multi.empty() || subs.multi.size() == 1) {
                // upwards propagation
                if (subs.multi.empty()) {
                    if (subs.tru.size() % 2 != 0) {
                        db[id].value = Valuation::TRUE;
                    } else {
                        db[id].value = Valuation::FALSE;
                    }
                } else {
                    db[id].value = Valuation::MULTIVARIATE;
                }
            } else {
                db[id].value = Valuation::MULTIVARIATE;
            }
        },
        [&](BOOL&) {},
        [&](CONSTRAINT&) {},
    }, db[id].content);

    if (old_value != db[id].value) {
        for (const auto pid : db[id].parents) {
            propagate_consistency(pid);
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

void NoopEvaluation::set_formula(const FormulaT& f) {
    formula = formula_noop_ds::to_formula_tree(m_proj, f);

    for (auto& [var, atoms] : formula.vartof) {
        if (var.type() == carl::VariableType::VT_REAL) {
            std::sort(atoms.begin(), atoms.end(), [&](const formula_noop_ds::FormulaID a, const formula_noop_ds::FormulaID b) {
                const auto& constr_a = std::get<formula_noop_ds::CONSTRAINT>(formula.db[a].content).constraint;
                const auto& constr_b = std::get<formula_noop_ds::CONSTRAINT>(formula.db[b].content).constraint;
                return m_constraint_complexity_ordering(m_proj, constr_a, constr_b);
            });
        }
    }

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Polynomials:" << m_proj.polys());

    SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update formula");
    for (formula_noop_ds::FormulaID i = 0; i < formula.db.size(); i++) {
        if (std::holds_alternative<formula_noop_ds::TRUE>(formula.db[i].content)) {
            formula.propagate_consistency(i);
        }
        if (std::holds_alternative<formula_noop_ds::FALSE>(formula.db[i].content)) {
            formula.propagate_consistency(i);
        }
    }
}


void NoopEvaluation::extend_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(assignment, ass);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
	if(root_valuation() != Valuation::MULTIVARIATE) return;
    auto atoms = formula.vartof.find(var);
    if (atoms == formula.vartof.end()) return;

    for (const auto id : atoms->second) {
        const auto& constr = std::get<formula_noop_ds::CONSTRAINT>(formula.db[id].content).constraint;
        assert (m_proj.main_var(constr.lhs) == var);

        SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Evaluate constraint " << constr);
        auto res = m_proj.evaluate(ass, constr);
        if (!boost::indeterminate(res)) {
            SMTRAT_LOG_TRACE("smtrat.covering_ng.evaluation", "Update formula");
            if (res) {
                formula.db[id].value = Valuation::TRUE;
            } else {
                formula.db[id].value = Valuation::FALSE;
            }
            
            //formula.propagate_consistency(id);
            for (const auto pid : formula.db[id].parents) {
                formula.propagate_consistency(pid);
            }
        }

        if (root_valuation() != Valuation::MULTIVARIATE) {
            break;
        }
    }
}

void NoopEvaluation::revert_valuation(const cadcells::Assignment& ass) {
    auto var = new_var(ass, assignment);
    assignment = ass; 
    if (var == carl::Variable::NO_VARIABLE) return;
    auto atomset = formula.vartof.find(var);
    if (atomset == formula.vartof.end()) return;

    for (const auto id : atomset->second) {
        formula.db[id].value = Valuation::MULTIVARIATE;
        //formula.propagate_consistency(id);
        for (const auto pid : formula.db[id].parents) {
            formula.propagate_consistency(pid);
        }
    }
}

std::vector<Implicant> NoopEvaluation::compute_implicants() {
    std::vector<Implicant> implicants;
    implicants.emplace_back();
    for (formula_noop_ds::FormulaID i = 0; i < formula.db.size(); i++) {
        if (std::holds_alternative<formula_noop_ds::CONSTRAINT>(formula.db[i].content) && std::get<formula_noop_ds::CONSTRAINT>(formula.db[i].content).constraint.lhs.level <= assignment.size()) {
            implicants.back().insert(std::get<formula_noop_ds::CONSTRAINT>(formula.db[i].content).constraint);
        }
    }
    return implicants;
}

Valuation NoopEvaluation::root_valuation() const {
    return formula.db.at(formula.root).value;
}

}