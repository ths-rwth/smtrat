#include "FormulaEvaluation.h"
#include <carl-arith/constraint/Conversion.h>

namespace smtrat::covering_ng::formula {

// helper type for the visitor
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
// explicit deduction guide (not needed as of C++20)
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

void sort_by_complexity(FormulaEvaluation& f, const std::function<bool(const FormulaEvaluation&, const FormulaEvaluation&)>& compare) {
    return std::visit(overloaded{
        [&](TRUE& c) {
            // TODO update
        },
        [&](FALSE& c) {
            // TODO update
        },
        [&](NOT& c) {
            sort_by_complexity(c.subformula, compare);
            // TODO update
        },
        [&](AND& c) {
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
            }
            // TODO sort
            // TODO update
        },
        [&](OR& c) {
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
            }
            // TODO sort
            // TODO update
        },
        [&](IFF& c) {
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
            }
            // TODO sort
            // TODO update
        },
        [&](XOR& c) {
            for (auto& sf : c.subformulas) {
                sort_by_complexity(sf, compare);
            }
            // TODO sort
            // TODO update
        },
        [&](BOOL& c) {
            // TODO update
        },
        [&](CONSTRAINT& c) {
            // TODO update
        },
    }, f.c().content);
}

/**
 * @brief Updates the valuations. Assumes that ass is an extension of the previous assignment the formula has been evaluated with.
 * 
 * @param f 
 * @param ass 
 */
void extend_valuation(FormulaEvaluation& f, const cadcells::Assignment& ass) {
    if (f.c().valuation == Valuation::TRUE || f.c().valuation == Valuation::FALSE) return;
    return std::visit(overloaded{
        [&](TRUE& c) {
            f.c().valuation = Valuation::TRUE;
        },
        [&](FALSE& c) {
            f.c().valuation = Valuation::FALSE;
        },
        [&](NOT& c) {
            extend_valuation(c.subformula, ass);
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
                extend_valuation(sf, ass);
                if (sf.c().valuation == Valuation::FALSE) {
                    f.c().valuation = Valuation::FALSE;
                    break;
                } else if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](OR& c) {
            f.c().valuation = Valuation::FALSE;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass);
                if (sf.c().valuation == Valuation::TRUE) {
                    f.c().valuation = Valuation::TRUE;
                    break;
                } else if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](IFF& c) {
            f.c().valuation = Valuation::UNKNOWN;
            Valuation reference = Valuation::UNKNOWN;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass);
                if (sf.c().valuation != Valuation::MULTIVARIATE) {
                    if (reference == Valuation::UNKNOWN) {
                        reference = sf.c().valuation;
                    } else if (reference == sf.c().valuation) {
                        f.c().valuation = Valuation::TRUE;
                    } else {
                        assert(reference != sf.c().valuation);
                        f.c().valuation = Valuation::FALSE;
                        break;
                    }
                } else {
                    f.c().valuation = Valuation::MULTIVARIATE;
                }
            }
        },
        [&](XOR& c) {
            f.c().valuation = Valuation::FALSE;
            for (auto& sf : c.subformulas) {
                extend_valuation(sf, ass);
                if (sf.c().valuation == Valuation::MULTIVARIATE) {
                    f.c().valuation = Valuation::MULTIVARIATE;
                    break;
                } else if (sf.c().valuation == Valuation::TRUE) {
                    f.c().valuation = Valuation::FALSE;
                } else {
                    assert(sf.c().valuation == Valuation::FALSE);
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

void revert_valuation(FormulaEvaluation& f, std::size_t level) {
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
            if (exists_true == exists_false && exists_multivariate) {
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

void compute_implicant(const FormulaEvaluation& f, std::vector<cadcells::Constraint>& implicant) {
    assert (f.c().valuation == Valuation::TRUE || f.c().valuation == Valuation::FALSE);
    return std::visit(overloaded{
        [&](const TRUE&) {
            // do nothing
        },
        [&](const FALSE&) {
            // do nothing
        },
        [&](const NOT& c) {
            std::vector<cadcells::Constraint> subimplicant;
            compute_implicant(c.subformula, subimplicant);
            for (const auto& si : subimplicant) {
                implicant.push_back(si.negation());
            }
        },
        [&](const AND& c) {
            for (const auto& sf : c.subformulas) {
                if (f.c().valuation == Valuation::FALSE && sf.c().valuation == Valuation::FALSE) {
                    compute_implicant(sf, implicant);
                    break;
                } else if (f.c().valuation == Valuation::TRUE) {
                    assert(sf.c().valuation == Valuation::TRUE);
                    compute_implicant(sf, implicant);
                }
            }
        },
        [&](const OR& c) {
            for (const auto& sf : c.subformulas) {
                if (f.c().valuation == Valuation::TRUE && sf.c().valuation == Valuation::TRUE) {
                    compute_implicant(sf, implicant);
                    break;
                } else if (f.c().valuation == Valuation::FALSE) {
                    assert(sf.c().valuation == Valuation::FALSE);
                    compute_implicant(sf, implicant);
                }
            }
        },
        [&](const IFF& c) {
            if (f.c().valuation == Valuation::TRUE) {
                for (const auto& sf : c.subformulas) {
                    compute_implicant(sf, implicant);
                }
            } else {
                bool found_true = false;
                bool found_false = false;
                for (const auto& sf : c.subformulas) {
                    if (sf.c().valuation == Valuation::TRUE && !found_true) {
                        compute_implicant(sf, implicant);
                        found_true = true;
                    } else if (sf.c().valuation == Valuation::TRUE && !found_false) {
                        compute_implicant(sf, implicant);
                        found_false = true;
                    }
                }
            }
        },
        [&](const XOR& c) {
            for (const auto& sf : c.subformulas) {
                assert(sf.c().valuation == Valuation::TRUE || sf.c().valuation == Valuation::FALSE);
                compute_implicant(sf, implicant);
            }
        },
        [&](const BOOL&) {
            assert(false);
        },
        [&](const CONSTRAINT& c) {
            if (f.c().valuation == Valuation::TRUE) {
                implicant.push_back(c.constraint);
            } else if (f.c().valuation == Valuation::FALSE) {
                implicant.push_back(c.constraint.negation());
            } else {
                assert(false);
            }
        },
    }, f.c().content);
}

FormulaEvaluation to_evaluation(typename cadcells::Polynomial::ContextType c, const FormulaT& f) {
    switch(f.type()) {
        case carl::FormulaType::ITE: {
            return to_evaluation(c, FormulaT(carl::FormulaType::OR, FormulaT(carl::FormulaType::AND, f.condition(), f.first_case()), FormulaT(carl::FormulaType::AND, f.condition().negated(), f.second_case())));
        }
        case carl::FormulaType::TRUE: {
            return FormulaEvaluation(TRUE{ });
        }
        case carl::FormulaType::FALSE: {
            return FormulaEvaluation(FALSE{ });
        }
        case carl::FormulaType::BOOL: {
            return FormulaEvaluation(BOOL{ f.boolean() });
        }
        case carl::FormulaType::NOT: {
            return FormulaEvaluation(NOT{ to_evaluation(c,f.subformula()) });
        }
        case carl::FormulaType::IMPLIES: {
            return to_evaluation(c, FormulaT(carl::FormulaType::OR, f.premise().negated(), f.conclusion()));
        }
        case carl::FormulaType::AND: {
            std::vector<FormulaEvaluation> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_evaluation(c,sf));
            }
            return FormulaEvaluation(AND{ std::move(subformulas) });
        }
        case carl::FormulaType::OR: {
            std::vector<FormulaEvaluation> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_evaluation(c,sf));
            }
            return FormulaEvaluation(OR{ std::move(subformulas) });
        }
        case carl::FormulaType::XOR: {
            std::vector<FormulaEvaluation> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_evaluation(c,sf));
            }
            return FormulaEvaluation(XOR{ std::move(subformulas) });
        }
        case carl::FormulaType::IFF: {
            std::vector<FormulaEvaluation> subformulas;
            for (const auto& sf : f.subformulas()) {
                subformulas.emplace_back(to_evaluation(c,sf));
            }
            return FormulaEvaluation(IFF{ std::move(subformulas) });
        }
        case carl::FormulaType::CONSTRAINT: {
            auto bc = carl::convert<cadcells::Polynomial>(c, f.constraint().constr());
            return FormulaEvaluation(CONSTRAINT{ bc });
        }
        default: {
            assert(false);
            return FormulaEvaluation(FALSE{});
        }
    }
}

} // namespace smtrat::coveringng::formula

#include "FormulaEvaluationComplexity.h"
