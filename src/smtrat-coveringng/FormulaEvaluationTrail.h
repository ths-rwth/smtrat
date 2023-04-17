#pragma once

namespace smtrat::covering_ng::formula {

namespace formula_ds {

using FormulaID = std::size_t;

// TODO store watchlists
struct TRUE {
    void init_watches() {}
};
struct FALSE {
    void init_watches() {}
};
struct NOT {
    FormulaID subformula;
    void init_watches() {
        // subscribe to subformula
        //TODO the subformula needs to subscribe to this formula as well??
    }
};
struct AND {
    std::vector<FormulaID> subformulas;
    void init_watches() {
        // subscribe to all subformulas
    }
};
struct OR {
    std::vector<FormulaID> subformulas;
    FormulaID watch_a;
    FormulaID watch_b;
    void init_watches() {
        // pick and subscribe to watch_a and watch_b
        // TODO should it watch it self as well??
    }
};
struct IFF {
    std::vector<FormulaID> subformulas;
    void init_watches() {
        // subscribe to all subformulas
    }
};
struct XOR {
    std::vector<FormulaID> subformulas;
    FormulaID watch;
    void init_watches() {
        // pick and subscribe to watch
    }
};
struct BOOL {
    carl::Variable variable;
    FormulaID negation; // TODO initialize at beginning
    void init_watches() {
        // subscribe to negation?
    }
};
struct CONSTRAINT {
    carl::BasicConstraint<cadcells::Polynomial> constraint;
    void init_watches() {
        // subscribe to other constraints... // TODO how?
    }
};

struct Formula {
    std::variant<TRUE,FALSE,NOT,AND,OR,IFF,XOR,BOOL,CONSTRAINT> content;
    Valuation valuation;
    boost::container::flat_set<FormulaID> subscribers; // TODO generalize -> not only parents, but all other subformulas where a propagation is possible! (i.e. conflicting relations of constraints, negations, etc)

    Formula(C&& c) : content(std::move(c)), valuation(Valuation::UNKNOWN) {};
};

using FormulaDB = std::vector<Formula>;
using VariableToFormula = boost::container::flat_map<carl::Variable, boost::container::flat_set<FormulaID>>;

using TrailElementID = std::size_t;
struct VariableDecision {
    carl::Variable variable;
    std::variant<RAN, bool> value;
};
struct FormulaAssignment {
    TrailElementID antecedent;
    FormulaID formula;
    bool value;
}

struct TrailElement {
    std::variant<FormulaAssignment,VariableAssignment> content;
};

using Trail = std::vector<TrailElement>;


// TODO maintain affects
FormulaID to_formula_db(typename cadcells::Polynomial::ContextType c, const FormulaT& f, FormulaDB& db, VariableToFormula& vartof, std::map<std::size_t,FormulaID>& cache) {
    {
        auto cache_it = cache.find(f.id());
        if (cache_it != cache.end()) return cache_it->second;
    }
    switch(f.type()) {
        case carl::FormulaType::ITE: {
            return to_formula_db(c, FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, f.condition(), f.first_case()), FormulaT(carl::FormulaType::AND, f.condition().negated(), f.second_case())), db, vartof, cache);
        }
        case carl::FormulaType::TRUE: {
            db.emplace_back(TRUE{ });
            return db.size()-1;
        }
        case carl::FormulaType::FALSE: {
            db.emplace_back(FALSE{ });
            return db.size()-1;
        }
        case carl::FormulaType::BOOL: {
            db.emplace_back(BOOL{ f.boolean() });
            vartof.try_emplace(f.boolean()).first->insert(db.size()-1);
            return db.size()-1;
        }
        case carl::FormulaType::NOT: {
            db.emplace_back(NOT{ to_formula_db(c,f.subformula(), cache) });
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
            db.emplace_back(AND{ std::move(subformulas) });
            return db.size()-1;
        }
        case carl::FormulaType::OR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(OR{ std::move(subformulas) });
            return db.size()-1;
        }
        case carl::FormulaType::XOR: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(XOR{ std::move(subformulas) });
            return db.size()-1;
        }
        case carl::FormulaType::IFF: {
            std::vector<FormulaID> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_formula_db(c,sf, db, vartof, cache));
            }
            db.emplace_back(IFF{ std::move(subformulas) });
            return db.size()-1;
        }
        case carl::FormulaType::CONSTRAINT: {
            auto bc = carl::convert<cadcells::Polynomial>(c, f.constraint().constr());
            db.emplace_back(CONSTRAINT{ bc });
            auto it = vartof.try_emplace(var).first;
            for (const auto& var : f.constraint().variables()) {
                it->insert(db.size()-1);
            }
            return db.size()-1;
        }
        default: {
            assert(false);
            db.emplace_back(FALSE{});
            return db.size()-1;
        }
    }
}


}

}