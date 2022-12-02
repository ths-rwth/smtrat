#include "FormulaEvaluation.h"
#include <carl-arith/constraint/Conversion.h>

namespace smtrat::covering_ng::formula {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


namespace node_ds {
/**
 * @brief Updates the valuations. Assumes that ass is an extension of the previous assignment the formula has been evaluated with.
 * 
 * @param f 
 * @param ass 
 */
void extend_valuation(Node& f, const cadcells::Assignment& ass, bool evaluate_all) {
    if (f.c().valuation == Valuation::TRUE || f.c().valuation == Valuation::FALSE) return;
    return std::visit(overloaded{
        [&](TRUE&) {
            f.c().valuation = Valuation::TRUE;
        },
        [&](FALSE&) {
            f.c().valuation = Valuation::FALSE;
        },
        [&](NOT& c) {
            extend_valuation(c.subformula, ass, evaluate_all);
            if (c.subformula.c().valuation == Valuation::TRUE) {
                f.c().valuation = Valuation::FALSE;
            } else if (c.subformula.c().valuation == Valuation::FALSE) {
                f.c().valuation = Valuation::TRUE;
            } else {
                assert(c.subformula.c().valuation == Valuation::MULTIVARIATE);
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
        [&](AND& c) {
            f.c().valuation = Valuation::TRUE;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass, evaluate_all);
                if (sf.c().valuation == Valuation::FALSE) {
                    f.c().valuation = Valuation::FALSE;
                    if (!evaluate_all)
                        break;
                } else if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    if (!evaluate_all || f.c().valuation != Valuation::FALSE)
                        f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](OR& c) {
            f.c().valuation = Valuation::FALSE;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass, evaluate_all);
                if (sf.c().valuation == Valuation::TRUE) {
                    f.c().valuation = Valuation::TRUE;
                    if (!evaluate_all)
                        break;
                } else if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    if (!evaluate_all || f.c().valuation != Valuation::TRUE)
                        f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](IFF& c) {
            f.c().valuation = Valuation::UNKNOWN;
            Valuation reference = Valuation::UNKNOWN;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass, evaluate_all);
                if (sf.c().valuation != Valuation::MULTIVARIATE) {
                    if (reference == Valuation::UNKNOWN) {
                        reference = sf.c().valuation;
                    } else if (reference == sf.c().valuation) {
                        f.c().valuation = Valuation::TRUE;
                    } else {
                        assert(reference != sf.c().valuation);
                        f.c().valuation = Valuation::FALSE;
                        if (!evaluate_all)
                            break;
                    }
                } else {
                    if (!evaluate_all || f.c().valuation != Valuation::FALSE)
                        f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](XOR& c) {
            f.c().valuation = Valuation::FALSE;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass, evaluate_all);
                if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    f.c().valuation = Valuation::MULTIVARIATE;
                    if (!evaluate_all) break;
                } else if (sf.c().valuation == Valuation::TRUE) {
                    if (!evaluate_all || f.c().valuation != Valuation::MULTIVARIATE)
                        f.c().valuation = Valuation::FALSE;
                } else {
                    assert(sf.c().valuation == Valuation::FALSE);
                    if (!evaluate_all || f.c().valuation != Valuation::MULTIVARIATE)
                        f.c().valuation = Valuation::TRUE;
                }
            }
        },
        [&](BOOL&) {
            f.c().valuation = Valuation::MULTIVARIATE;
        },
        [&](CONSTRAINT& c) {
            if (carl::level_of(c.constraint.lhs()) > ass.size()) {
                f.c().valuation = Valuation::MULTIVARIATE;
            } else {
                auto eval = carl::evaluate(c.constraint, ass);
                assert (!indeterminate(eval));
                if (!eval) f.c().valuation = Valuation::FALSE;
                else f.c().valuation = Valuation::TRUE;
            }
        },
    }, f.c().content);
}

void revert_valuation(Node& f, std::size_t level) {
    return std::visit(overloaded{
        [&](TRUE&) {
            // do nothing
        },
        [&](FALSE&) {
            // do nothing
        },
        [&](NOT& c) {
            revert_valuation(c.subformula, level);
            if (c.subformula.c().valuation == Valuation::MULTIVARIATE) {
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
        [&](AND& c) {
            bool exists_false = false;
            for (auto& sf : c.subformulas) {
                revert_valuation(sf, level);
                if (sf.c().valuation == Valuation::FALSE) {
                    exists_false = true;
                }
            }
            if (!exists_false) {
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
        [&](OR& c) {
            bool exists_true = false;
            for (auto& sf : c.subformulas) {
                revert_valuation(sf, level);
                if (sf.c().valuation == Valuation::TRUE) {
                    exists_true = true;
                }
            }
            if (!exists_true) {
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
        [&](IFF& c) {
            bool exists_false = false;
            bool exists_true = false;
            bool exists_multivariate = false;
            for (auto& sf : c.subformulas) {
                revert_valuation(sf, level);
                if (sf.c().valuation == Valuation::TRUE) {
                    exists_true = true;
                } else if (sf.c().valuation == Valuation::FALSE) {
                    exists_false = true;
                } else if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    exists_multivariate = true;
                }
            }
            if (!(exists_true && exists_false) && exists_multivariate) {
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
        [&](XOR& c) {
            for (auto& sf : c.subformulas) {
                revert_valuation(sf, level);
                if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](BOOL&) {
            f.c().valuation = Valuation::MULTIVARIATE;
        },
        [&](CONSTRAINT& c) {
            if (carl::level_of(c.constraint.lhs()) > level) {
                f.c().valuation = Valuation::MULTIVARIATE;
            }
        },
    }, f.c().content);
}

Node to_node(typename cadcells::Polynomial::ContextType c, const FormulaT& f, std::map<std::size_t,Node>& cache) {
    {
        auto cache_it = cache.find(f.id());
        if (cache_it != cache.end()) return cache_it->second;
    }
    switch(f.type()) {
        case carl::FormulaType::ITE: {
            return to_node(c, FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, f.condition(), f.first_case()), FormulaT(carl::FormulaType::AND, f.condition().negated(), f.second_case())), cache);
        }
        case carl::FormulaType::TRUE: {
            return Node(TRUE{ });
        }
        case carl::FormulaType::FALSE: {
            return Node(FALSE{ });
        }
        case carl::FormulaType::BOOL: {
            return Node(BOOL{ f.boolean() });
        }
        case carl::FormulaType::NOT: {
            return Node(NOT{ to_node(c,f.subformula(), cache) });
        }
        case carl::FormulaType::IMPLIES: {
            return to_node(c, FormulaT(carl::FormulaType::OR, f.premise().negated(), f.conclusion()), cache);
        }
        case carl::FormulaType::AND: {
            std::vector<Node> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_node(c,sf, cache));
            }
            return Node(AND{ std::move(subformulas) });
        }
        case carl::FormulaType::OR: {
            std::vector<Node> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_node(c,sf, cache));
            }
            return Node(OR{ std::move(subformulas) });
        }
        case carl::FormulaType::XOR: {
            std::vector<Node> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_node(c,sf, cache));
            }
            return Node(XOR{ std::move(subformulas) });
        }
        case carl::FormulaType::IFF: {
            std::vector<Node> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_node(c,sf, cache));
            }
            return Node(IFF{ std::move(subformulas) });
        }
        case carl::FormulaType::CONSTRAINT: {
            auto bc = carl::convert<cadcells::Polynomial>(c, f.constraint().constr());
            return Node(CONSTRAINT{ bc });
        }
        default: {
            assert(false);
            return Node(FALSE{});
        }
    }
}

Node to_node(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    std::map<std::size_t,Node> cache;
    return to_node(c, f, cache);
}

}


/** Minimal **/
namespace minimal_helper {

void sort_by_complexity(node_ds::Node& f, const std::function<bool(const node_ds::Node&, const node_ds::Node&)>& compare) {
    return std::visit(overloaded{
        [&](node_ds::TRUE&) {
            f.c().num_subformulas = 1;
        },
        [&](node_ds::FALSE&) {
            f.c().num_subformulas = 1;
        },
        [&](node_ds::NOT& c) {
            sort_by_complexity(c.subformula, compare);
            f.c().max_level = c.subformula.c().max_level;
            f.c().max_degree = c.subformula.c().max_degree;
            f.c().max_total_degree = c.subformula.c().max_total_degree;
            f.c().num_subformulas = c.subformula.c().num_subformulas + 1;
            f.c().num_constraints = c.subformula.c().num_constraints;
            f.c().boolean_variables = c.subformula.c().boolean_variables;
            f.c().arithmetic_variables = c.subformula.c().arithmetic_variables;
        },
        [&](node_ds::AND& c) {
            f.c().num_subformulas = 1;
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
                f.c().max_level = std::max(f.c().max_level, sf.c().max_level);
                f.c().max_degree = std::max(f.c().max_degree, sf.c().max_degree);
                f.c().max_total_degree = std::max(f.c().max_total_degree, sf.c().max_total_degree);
                f.c().num_subformulas += sf.c().num_subformulas;
                f.c().num_constraints += sf.c().num_constraints;
                f.c().boolean_variables.insert(sf.c().boolean_variables.begin(), sf.c().boolean_variables.end());
                f.c().arithmetic_variables.insert(sf.c().arithmetic_variables.begin(), sf.c().arithmetic_variables.end());
            }
            std::sort(c.subformulas.begin(), c.subformulas.end(), compare);
        },
        [&](node_ds::OR& c) {
            f.c().num_subformulas = 1;
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
                f.c().max_level = std::max(f.c().max_level, sf.c().max_level);
                f.c().max_degree = std::max(f.c().max_degree, sf.c().max_degree);
                f.c().max_total_degree = std::max(f.c().max_total_degree, sf.c().max_total_degree);
                f.c().num_subformulas += sf.c().num_subformulas;
                f.c().num_constraints += sf.c().num_constraints;
                f.c().boolean_variables.insert(sf.c().boolean_variables.begin(), sf.c().boolean_variables.end());
                f.c().arithmetic_variables.insert(sf.c().arithmetic_variables.begin(), sf.c().arithmetic_variables.end());
            }
            std::sort(c.subformulas.begin(), c.subformulas.end(), compare);
        },
        [&](node_ds::IFF& c) {
            f.c().num_subformulas = 1;
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
                f.c().max_level = std::max(f.c().max_level, sf.c().max_level);
                f.c().max_degree = std::max(f.c().max_degree, sf.c().max_degree);
                f.c().max_total_degree = std::max(f.c().max_total_degree, sf.c().max_total_degree);
                f.c().num_subformulas += sf.c().num_subformulas;
                f.c().num_constraints += sf.c().num_constraints;
                f.c().boolean_variables.insert(sf.c().boolean_variables.begin(), sf.c().boolean_variables.end());
                f.c().arithmetic_variables.insert(sf.c().arithmetic_variables.begin(), sf.c().arithmetic_variables.end());
            }
            std::sort(c.subformulas.begin(), c.subformulas.end(), compare);
        },
        [&](node_ds::XOR& c) {
            f.c().num_subformulas = 1;
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
                f.c().max_level = std::max(f.c().max_level, sf.c().max_level);
                f.c().max_degree = std::max(f.c().max_degree, sf.c().max_degree);
                f.c().max_total_degree = std::max(f.c().max_total_degree, sf.c().max_total_degree);
                f.c().num_subformulas += sf.c().num_subformulas;
                f.c().num_constraints += sf.c().num_constraints;
                f.c().boolean_variables.insert(sf.c().boolean_variables.begin(), sf.c().boolean_variables.end());
                f.c().arithmetic_variables.insert(sf.c().arithmetic_variables.begin(), sf.c().arithmetic_variables.end());
            }
            std::sort(c.subformulas.begin(), c.subformulas.end(), compare);
        },
        [&](node_ds::BOOL& c) {
            f.c().num_subformulas = 1;
            f.c().boolean_variables.insert(c.variable);
        },
        [&](node_ds::CONSTRAINT& c) {
            f.c().max_level = carl::level_of(c.constraint.lhs());
            f.c().max_degree = c.constraint.lhs().degree();
            f.c().max_total_degree = c.constraint.lhs().total_degree();
            f.c().num_subformulas = 1;
            f.c().num_constraints = 1;
            auto vars = carl::arithmetic_variables(c.constraint);
            f.c().arithmetic_variables.insert(vars.begin(), vars.end());
        },
    }, f.c().content);
}

}

void Minimal::set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    m_root = node_ds::to_node(c, f);
    minimal_helper::sort_by_complexity(*m_root, m_formula_complexity_ordering);
}
void Minimal::extend_valuation(const cadcells::Assignment& ass) {
    return node_ds::extend_valuation(*m_root, ass, false);
}
void Minimal::revert_valuation(std::size_t level) {
    return node_ds::revert_valuation(*m_root, level);
}
namespace minimal_helper {

void compute_implicant(const node_ds::Node& f, boost::container::flat_set<cadcells::Constraint>& implicant) {
    assert (f.c().valuation == Valuation::TRUE || f.c().valuation == Valuation::FALSE);
    return std::visit(overloaded{
        [&](const node_ds::TRUE&) {
            // do nothing
        },
        [&](const node_ds::FALSE&) {
            // do nothing
        },
        [&](const node_ds::NOT& c) {
            boost::container::flat_set<cadcells::Constraint> sub_implicant;
            compute_implicant(c.subformula, sub_implicant);
            for (const auto& si : sub_implicant) {
                implicant.insert(si.negation());
            }
        },
        [&](const node_ds::AND& c) {
            if (f.c().valuation == Valuation::FALSE) {
                boost::container::flat_set<cadcells::Constraint> sub_implicant;
                for (auto sf = c.subformulas.rbegin(); sf != c.subformulas.rend(); sf++) {
                    if (sf->c().valuation == Valuation::FALSE) {
                        sub_implicant.clear();
                        compute_implicant(*sf, sub_implicant);
                        if (std::includes(implicant.begin(), implicant.end(), sub_implicant.begin(), sub_implicant.end())) {
                            sub_implicant.clear();
                            break;
                        }
                    }
                }
                implicant.insert(sub_implicant.begin(), sub_implicant.end());
            } else if (f.c().valuation == Valuation::TRUE) {
                for (const auto& sf : c.subformulas) {
                    assert(sf.c().valuation == Valuation::TRUE);
                    compute_implicant(sf, implicant);
                }
            }
        },
        [&](const node_ds::OR& c) {
            if (f.c().valuation == Valuation::TRUE) {
                boost::container::flat_set<cadcells::Constraint> sub_implicant;
                for (auto sf = c.subformulas.rbegin(); sf != c.subformulas.rend(); sf++) {
                    if (sf->c().valuation == Valuation::TRUE) {
                        sub_implicant.clear();
                        compute_implicant(*sf, sub_implicant);
                        if (std::includes(implicant.begin(), implicant.end(), sub_implicant.begin(), sub_implicant.end())) {
                            sub_implicant.clear();
                            break;
                        }
                    }
                }
                implicant.insert(sub_implicant.begin(), sub_implicant.end());
            } else if (f.c().valuation == Valuation::FALSE) {
                for (const auto& sf : c.subformulas) {
                    assert(sf.c().valuation == Valuation::FALSE);
                    compute_implicant(sf, implicant);
                }
            }
        },
        [&](const node_ds::IFF& c) {
            if (f.c().valuation == Valuation::TRUE) {
                for (const auto& sf : c.subformulas) {
                    compute_implicant(sf, implicant);
                }
            } else {
                boost::container::flat_set<cadcells::Constraint> sub_implicant_true;
                boost::container::flat_set<cadcells::Constraint> sub_implicant_false;
                bool found_true = false;
                bool found_false = false;
                for (auto sf = c.subformulas.rbegin(); sf != c.subformulas.rend(); sf++) {
                    if (sf->c().valuation == Valuation::TRUE && !found_true) {
                        sub_implicant_true.clear();
                        compute_implicant(*sf, sub_implicant_true);
                        if (std::includes(implicant.begin(), implicant.end(), sub_implicant_true.begin(), sub_implicant_true.end())) {
                            found_true = true;
                            sub_implicant_true.clear();
                        }
                    } else if (sf->c().valuation == Valuation::FALSE && !found_false) {
                        sub_implicant_false.clear();
                        compute_implicant(*sf, sub_implicant_false);
                        if (std::includes(implicant.begin(), implicant.end(), sub_implicant_false.begin(), sub_implicant_false.end())) {
                            found_false = true;
                            sub_implicant_false.clear();
                        }
                    }
                }
                implicant.insert(sub_implicant_true.begin(), sub_implicant_true.end());
                implicant.insert(sub_implicant_false.begin(), sub_implicant_false.end());
            }
        },
        [&](const node_ds::XOR& c) {
            for (const auto& sf : c.subformulas) {
                assert(sf.c().valuation == Valuation::TRUE || sf.c().valuation == Valuation::FALSE);
                compute_implicant(sf, implicant);
            }
        },
        [&](const node_ds::BOOL&) {
            assert(false);
        },
        [&](const node_ds::CONSTRAINT& c) {
            if (f.c().valuation == Valuation::TRUE) {
                implicant.insert(c.constraint);
            } else if (f.c().valuation == Valuation::FALSE) {
                implicant.insert(c.constraint.negation());
            } else {
                assert(false);
            }
        },
    }, f.c().content);
}

}
boost::container::flat_set<cadcells::Constraint> Minimal::compute_implicant() const {
    boost::container::flat_set<cadcells::Constraint> implicant;
    minimal_helper::compute_implicant(*m_root, implicant);
    return implicant;
}
Valuation Minimal::root_valuation() const {
    return m_root->c().valuation;
}


/** ExhaustiveImplicants **/

void ExhaustiveImplicants::set_formula(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    m_root = node_ds::to_node(c, f);
}
void ExhaustiveImplicants::extend_valuation(const cadcells::Assignment& ass) {
    return node_ds::extend_valuation(*m_root, ass, true);
}
void ExhaustiveImplicants::revert_valuation(std::size_t level) {
    return node_ds::revert_valuation(*m_root, level);
}

namespace exhaustive_implicants_helper {

// TODO store only ids of constraints / change data structure
void compute_implicants(const node_ds::Node& f, std::vector<boost::container::flat_set<cadcells::Constraint>>& implicants) {
    // TODO pruning?
    assert (f.c().valuation == Valuation::TRUE || f.c().valuation == Valuation::FALSE);
    return std::visit(overloaded{
        [&](const node_ds::TRUE&) {
            // do nothing
        },
        [&](const node_ds::FALSE&) {
            // do nothing
        },
        [&](const node_ds::NOT& c) {
            std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants;
            compute_implicants(c.subformula, sub_implicants);
            for (const auto& sub_implicant : sub_implicants) {
                boost::container::flat_set<cadcells::Constraint> implicant;
                for (const auto& si : sub_implicant) {
                    implicant.insert(si.negation());
                }
                implicants.push_back(implicant);
            }
        },
        [&](const node_ds::AND& c) {
            if (f.c().valuation == Valuation::FALSE) {
                for (const auto& sf : c.subformulas) {
                    if (sf.c().valuation == Valuation::FALSE) {
                        compute_implicants(sf, implicants);
                    }
                }
            } else if (f.c().valuation == Valuation::TRUE) {
                std::vector<boost::container::flat_set<cadcells::Constraint>> new_implicants;
                for (const auto& sf : c.subformulas) {
                    assert(sf.c().valuation == Valuation::TRUE);
                    std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants;
                    compute_implicants(sf, sub_implicants);
                    auto size = new_implicants.size();
                    if (size == 0) {
                        new_implicants.insert(new_implicants.end(), sub_implicants.begin(), sub_implicants.end());
                    } else {
                        for (std::size_t j = 1; j < sub_implicants.size(); j++) {
                            for (std::size_t i = 0; i < size; i++) {
                                new_implicants.back().insert(new_implicants[i].begin(), new_implicants[i].end());
                            }
                        }
                        std::size_t i = 0;
                        for (const auto& sub_implicant : sub_implicants) {
                            new_implicants[i].insert(sub_implicant.begin(), sub_implicant.end());
                            i++;
                        }
                    }
                }
                // TODO remove duplicates
                implicants.insert(implicants.end(), new_implicants.begin(), new_implicants.end());
            }
        },
        [&](const node_ds::OR& c) {
            if (f.c().valuation == Valuation::TRUE) {
                for (const auto& sf : c.subformulas) {
                    if (sf.c().valuation == Valuation::TRUE) {
                        compute_implicants(sf, implicants);
                    }
                }
            } else if (f.c().valuation == Valuation::FALSE) {
                std::vector<boost::container::flat_set<cadcells::Constraint>> new_implicants;
                for (const auto& sf : c.subformulas) {
                    assert(sf.c().valuation == Valuation::FALSE);
                    std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants;
                    compute_implicants(sf, sub_implicants);
                    auto size = new_implicants.size();
                    if (size == 0) {
                        new_implicants.insert(new_implicants.end(), sub_implicants.begin(), sub_implicants.end());
                    } else {
                        for (std::size_t j = 1; j < sub_implicants.size(); j++) {
                            for (std::size_t i = 0; i < size; i++) {
                                new_implicants.back().insert(new_implicants[i].begin(), new_implicants[i].end());
                            }
                        }
                        std::size_t i = 0;
                        for (const auto& sub_implicant : sub_implicants) {
                            new_implicants[i].insert(sub_implicant.begin(), sub_implicant.end());
                            i++;
                        }
                    }
                }
                // TODO remove duplicates
                implicants.insert(implicants.end(), new_implicants.begin(), new_implicants.end());
            }
        },
        [&](const node_ds::IFF& c) {
            if (f.c().valuation == Valuation::TRUE) {
                std::vector<boost::container::flat_set<cadcells::Constraint>> new_implicants;
                for (const auto& sf : c.subformulas) {
                    std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants;
                    compute_implicants(sf, sub_implicants);
                    auto size = new_implicants.size();
                    for (std::size_t i = 0; i < size; i++) {
                        for (const auto& sub_implicant : sub_implicants) {
                            new_implicants.emplace_back();
                            new_implicants.back().insert(new_implicants[i].begin(), new_implicants[i].end());
                            new_implicants.back().insert(sub_implicant.begin(), sub_implicant.end());
                        }
                    }
                }
                // TODO remove duplicates
                implicants.insert(implicants.end(), new_implicants.begin(), new_implicants.end());
            } else {
                std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants_true;
                std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants_false;
                for (const auto& sf : c.subformulas) {
                    if (sf.c().valuation == Valuation::TRUE) {
                        compute_implicants(sf, sub_implicants_true);
                    } else if (sf.c().valuation == Valuation::FALSE) {
                        compute_implicants(sf, sub_implicants_false);
                    }
                }
                for (const auto& sub_implicant_true : sub_implicants_true) {
                    for (const auto& sub_implicant_false : sub_implicants_false) {
                        implicants.emplace_back();
                        implicants.back().insert(sub_implicant_true.begin(), sub_implicant_true.end());
                        implicants.back().insert(sub_implicant_false.begin(), sub_implicant_false.end());
                    }    
                }
                // TODO remove duplicates
            }
        },
        [&](const node_ds::XOR& c) {
            std::vector<boost::container::flat_set<cadcells::Constraint>> new_implicants;
            for (const auto& sf : c.subformulas) {
                assert(sf.c().valuation == Valuation::TRUE || sf.c().valuation == Valuation::FALSE);
                std::vector<boost::container::flat_set<cadcells::Constraint>> sub_implicants;
                compute_implicants(sf, sub_implicants);
                auto size = new_implicants.size();
                for (std::size_t i = 0; i < size; i++) {
                    for (const auto& sub_implicant : sub_implicants) {
                        new_implicants.emplace_back();
                        new_implicants.back().insert(new_implicants[i].begin(), new_implicants[i].end());
                        new_implicants.back().insert(sub_implicant.begin(), sub_implicant.end());
                    }
                }
            }
            implicants.insert(implicants.end(), new_implicants.begin(), new_implicants.end());
        },
        [&](const node_ds::BOOL&) {
            assert(false);
        },
        [&](const node_ds::CONSTRAINT& c) {
            if (f.c().valuation == Valuation::TRUE) {
                implicants.emplace_back(boost::container::flat_set<cadcells::Constraint>({c.constraint}));
            } else if (f.c().valuation == Valuation::FALSE) {
                implicants.emplace_back(boost::container::flat_set<cadcells::Constraint>({c.constraint.negation()}));
            } else {
                assert(false);
            }
        },
    }, f.c().content);
}
}

boost::container::flat_set<cadcells::Constraint> ExhaustiveImplicants::compute_implicant() const {
    std::vector<boost::container::flat_set<cadcells::Constraint>> implicants;
    exhaustive_implicants_helper::compute_implicants(*m_root, implicants);
    assert(implicants.size()>0);
    return *std::min_element(implicants.begin(), implicants.end(), m_implicant_complexity_ordering);
}
Valuation ExhaustiveImplicants::root_valuation() const {
    return m_root->c().valuation;
}

} // namespace smtrat::coveringng::formula

#include "FormulaEvaluation.h"
