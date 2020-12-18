#pragma once

#include <smtrat-common/smtrat-common.h>
#include <smtrat-common/model.h>
#include <carl-model/evaluation/ModelEvaluation.h>
#include <smtrat-cad/projectionoperator/utils.h>
#include <carl-covering/carl-covering.h>
#include <carl/ran/interval/ran_interval_extra.h>
#include "../OneCellCAD.h"


namespace smtrat {
namespace mcsat {
namespace onecellcad{
namespace firstlevel {

using carl::operator<<;

using RAN = carl::RealAlgebraicNumber<Rational>;

struct indexed_root {
    Poly poly;
    size_t index;
};
std::ostream& operator<<(std::ostream& os, const indexed_root& data) {
    os << "root(" << data.poly << ", " << data.index << ")";
    return os;
}

// TODO datastructures are inefficient: maybe introduce datastructure representing polynomials on a level, avoid double storing polys
// TODO more flexible orderings

// TODO use projection candidates instead of computing the actual projections? then, some double computations could be saved

// TODO use inheritance instead of variant? OR: use intervals instead of section/sector
struct section {
    std::vector<Poly> current_level;
    std::vector<Poly> lower_level;

    indexed_root point_defining_poly;
    RAN point;
    std::set<Poly> others;
};
std::ostream& operator<<(std::ostream& os, const section& data) {
    os << "section(" << data.point_defining_poly << " [" << data.point << "], others = " << data.others << ", lower_level = " <<  data.lower_level << ")";
    return os;
}
struct sector {
    std::vector<Poly> current_level;
    std::vector<Poly> lower_level;

    std::optional<indexed_root> left_defining_poly;
    std::optional<indexed_root> right_defining_poly;
    std::optional<RAN> left;
    std::optional<RAN> right;
    std::set<Poly> others_left;
    std::set<Poly> others_right;
};
std::ostream& operator<<(std::ostream& os, const sector& data) {
    os << "sector(";
    if (data.left) {
        os << *data.left_defining_poly << " [" << *data.left << "]";
    } else {
        os << "-infty";
    }
    os << ", ";
    if (data.right) {
        os << *data.right_defining_poly << " [" << *data.right << "]";
    } else {
        os << "+infty";
    }
    os << ", others_left = " << data.others_left << ", others_right = " << data.others_right << ", lower_level = " <<  data.lower_level << ")";
    return os;
}
using cell_at_level = std::variant<section,sector>;
std::ostream& operator<<(std::ostream& os, const cell_at_level& data) {
    if (std::holds_alternative<sector>(data)) {
        os << std::get<sector>(data);
    } else {
        os << std::get<section>(data);
    }
    return os;
}
std::ostream& operator<<(std::ostream& os, const cell_at_level* data) {
    os << *data;
    return os;
}


class root_indexer {
    struct sample {
        RAN val;
        std::optional<const RAN*> left;
        std::optional<const RAN*> right;
        sample (RAN val,std::optional<const RAN*> left,std::optional<const RAN*> right) : val(val), left(left), right(right) {}
        bool is_point() const {
            return left && right && *left == *right;
        }
    };

    std::vector<RAN> m_roots;
    std::map<RAN, std::vector<indexed_root>> m_root_map;
    std::vector<sample> m_samples;

public:

    void insert_root(const RAN& ran, const indexed_root&& root) {
        assert(m_samples.empty());
        auto it = m_root_map.find(ran);
        if (it == m_root_map.end()) {
            m_root_map.emplace(ran, std::vector<indexed_root>({root}));
            m_roots.emplace_back(ran);
        } else {
            it->second.emplace_back(std::move(root));
        }
    }

    void process() {
        assert(m_samples.empty());
        std::sort(m_roots.begin(), m_roots.end());
        m_samples.reserve(2 * m_roots.size() + 1);
        for (std::size_t n = 0; n < m_roots.size(); n++) {
            if (n == 0) m_samples.emplace_back(carl::sample_below(m_roots.front()), std::nullopt, &m_roots.front());
            else m_samples.emplace_back(carl::sample_between(m_roots[n-1], m_roots[n]), &m_roots[n-1], &m_roots[n]);
            m_samples.emplace_back(m_roots[n], &m_roots[n], &m_roots[n]);
        }
        if (m_roots.empty()) m_samples.emplace_back(RAN(0), std::nullopt, std::nullopt);
        else m_samples.emplace_back(carl::sample_above(m_roots.back()), &m_roots.back(), std::nullopt);
    }

    const auto& samples() {
        return m_samples;
    }

    const auto& roots() {
        return m_roots;
    }

    const auto& indexed_roots_at(const RAN& ran) {
        return m_root_map.at(ran);
    }
    
    friend std::ostream& operator<<(std::ostream& os, const root_indexer::sample& data);
    friend std::ostream& operator<<(std::ostream& os, const root_indexer& data);

};
std::ostream& operator<<(std::ostream& os, const root_indexer::sample& data) {
    if (data.is_point()) {
        os << "[" << **data.left << "]";
    } else {
        os << "(";
        if (data.left) {
            os << **data.left;
        } else {
            os << "-infty";
        }
        os << ", ";
        if (data.right) {
            os << **data.right;
        } else {
            os << "+infty";
        }
        os << ")";
    }
    return os;
}
std::ostream& operator<<(std::ostream& os, const root_indexer& data) {
    os << "Root indexer" << std::endl;
    os << "Roots: " << data.m_roots << std::endl;
    os << "Root map: " << data.m_root_map << std::endl;
    os << "Samples: " << data.m_samples << std::endl;
    return os;
}

auto as_ran_map(const Model& model) {
    carl::ran::RANMap<Rational> eval_map;
    for (const auto& [key, value] : model) {
        eval_map.emplace(key.asVariable(), value.asRAN());
    }
    return eval_map;
}

bool var_subset(const carl::Variables& vars, const Model& model, carl::Variable var) {
    for (const auto& v : vars) {
        if (model.find(v) == model.end() && v != var) return false;
    }
    return true;
}


bool compute_unsat_intervals(const VariableComparisonT& constr, const Model& model, carl::Variable variable, std::vector<cell_at_level>& results) {
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Compute unsat intervals of " << constr);

    if (constr.var() != variable) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Does not have variable");
        return false;
    }
    carl::Variables vars;
    constr.collectVariables(vars);
    if (!var_subset(vars, model, variable)) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Contains unassigned variables");
        return false;
    }
    if (carl::ran::interval::vanishes(carl::to_univariate_polynomial(constr.definingPolynomial(), variable), as_ran_map(model))) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Vanishes");
        return false;
    }
    auto eval = carl::model::evaluate(FormulaT(constr), model);
    if (eval.isBool()) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Already evaluates to a constant"); // TODO is this case possible?
        return false;
    }

    assert(carl::irreducibleFactors(constr.definingPolynomial(), false).size() == 1);

    RAN ran;
    indexed_root ir;
    if (std::holds_alternative<RAN>(constr.value())) {
        ran = std::get<RAN>(constr.value());
        size_t index = 1; // TODO determine index, not relevant for covering
        ir = indexed_root({ constr.definingPolynomial(), index });
    } else {
        assert(std::holds_alternative<MultivariateRootT>(constr.value()));
        ir = indexed_root({ constr.definingPolynomial(), std::get<MultivariateRootT>(constr.value()).k() });

        auto res = std::get<MultivariateRootT>(constr.value()).evaluate(as_ran_map(model));
        assert(res);
        ran = *res;
    }

    auto relation = constr.negated() ? carl::inverse(constr.relation()) : constr.relation();
    bool point = relation == carl::Relation::GREATER || relation == carl::Relation::LESS || relation == carl::Relation::NEQ;
    bool below = relation == carl::Relation::GREATER || relation == carl::Relation::GEQ || relation == carl::Relation::EQ;
    bool above = relation == carl::Relation::LESS || relation == carl::Relation::LEQ || relation == carl::Relation::EQ;

    if (point) {
        section sec;
        sec.current_level.push_back(ir.poly);
        sec.point = ran; 
        sec.point_defining_poly = ir;
        results.push_back(sec);
    }
    if (below) {
        sector sec;
        sec.current_level.push_back(ir.poly);
        sec.right = ran; 
        sec.right_defining_poly = ir;
        results.push_back(sec);
    }
    if (above) {
        sector sec;
        sec.current_level.push_back(ir.poly);
        sec.left = ran; 
        sec.left_defining_poly = ir;
        results.push_back(sec);
    }
    return true;
}

bool compute_unsat_intervals(const ConstraintT& constr, const Model& model, carl::Variable variable, std::vector<cell_at_level>& results) {
    assert(!carl::is_zero(constr.lhs()));
    assert(!carl::is_constant(constr.lhs()));
    
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Compute unsat intervals of " << constr);

    if (!constr.lhs().has(variable)) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Does not have variable");
        return false;
    }
    auto vars_tmp = constr.variables().underlyingVariables();
    carl::Variables vars(vars_tmp.begin(), vars_tmp.end());
    if (!var_subset(vars, model, variable)) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Contains unassigned variables");
        return false;
    }
    if (carl::ran::interval::vanishes(carl::to_univariate_polynomial(constr.lhs(), variable), as_ran_map(model))) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Vanishes");
        return false;
    }
    // this is stronger than in CAC / OneCell: (not only nullification)
    auto eval = carl::model::evaluate(constr, model);
    if (eval.isBool()) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Already evaluates to a constant");
        if (!eval.asBool()) {
            SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Already evaluates to false");
            sector sec;
            auto factors = carl::irreducibleFactors(constr.lhs(), false);
            for (const auto& f : factors) {
                if (!f.has(variable)) {
                    sec.lower_level.push_back(f);
                } else {
                    sec.current_level.push_back(f);
                }
            }
            results.push_back(sec);
        }
        return true;
    }
 
    std::vector<Poly> lower_level;
    std::vector<Poly> current_level;

    root_indexer ri;
    auto factors = carl::irreducibleFactors(constr.lhs(), false);
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Computed factors " << factors);

    for (const auto& f : factors) {
        if (!f.has(variable)) {
            SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Factor " << f << " is of lower level");
            lower_level.push_back(f);
        } else {
            current_level.push_back(f);
            auto f_roots = carl::model::real_roots(f, variable, model);
            assert(f_roots.is_univariate());
            SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Factor " << f << " has roots " << f_roots.roots());
            for (size_t index = 0; index < f_roots.roots().size(); index++) {
                ri.insert_root(f_roots.roots()[index], indexed_root({f, index}));
            }
        }
    }

    ri.process();
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Got " << ri);
    for (const auto& s : ri.samples()) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Plugging in sample " << s);
        if (s.is_point()) {
            if (!carl::evaluate(carl::Sign::ZERO, constr.relation())) {
                section sec;
                sec.lower_level = lower_level;
                sec.current_level = current_level;
                {
                    sec.point = s.val;
                    const auto& indexed_roots = ri.indexed_roots_at(sec.point);
                    sec.point_defining_poly = indexed_roots.front();
                }
                for (const auto& os : ri.roots()) {
                    const auto& indexed_roots = ri.indexed_roots_at(os);
                    for (auto o = indexed_roots.begin()+1; o != indexed_roots.end(); o++) {
                        if (o->poly != sec.point_defining_poly.poly) {
                            sec.others.insert(o->poly);
                        }
                    }
                }
                results.push_back(sec);
            }
        } else {
            Model extended_model = model;
            extended_model.assign(variable, s.val);
            auto res = carl::model::evaluate(constr, extended_model);
            assert(res.isBool());
            if (!res.asBool()) {
                sector sec;
                sec.lower_level = lower_level;
                sec.current_level = current_level;
                if (s.left) {
                    sec.left = **s.left;
                    const auto& indexed_roots = ri.indexed_roots_at(*sec.left);
                    sec.left_defining_poly = indexed_roots.front();
                }
                if (s.right) {
                    sec.right = **s.right;
                    const auto& indexed_roots = ri.indexed_roots_at(*sec.right);
                    sec.right_defining_poly = indexed_roots.front();
                }
                bool left_of_sector = (bool) s.left;
                for (const auto& os : ri.roots()) {
                    const auto& indexed_roots = ri.indexed_roots_at(os);
                    for (auto o = indexed_roots.begin(); o != indexed_roots.end(); o++) {
                        if (left_of_sector) {
                            assert(s.left);
                            if (o->poly != sec.left_defining_poly->poly) {
                                sec.others_left.insert(o->poly);
                            }
                        } else {
                            assert(s.right);
                            if (o->poly != sec.right_defining_poly->poly) {
                                sec.others_right.insert(o->poly);
                            }
                        }
                    }
                    if (os == sec.left) {
                        left_of_sector = false;
                    }
                }
                results.push_back(sec);
            }
        }
    }
    return true;
}

bool compute_unsat_intervals(const FormulaT& constr, const Model& model, carl::Variable variable, std::vector<cell_at_level>& results) {
    if (constr.getType() == carl::FormulaType::CONSTRAINT) {
        return compute_unsat_intervals(constr.constraint(), model, variable, results);
    } else if (constr.getType() == carl::FormulaType::VARCOMPARE) {
        return compute_unsat_intervals(constr.variableComparison(), model, variable, results);
    } else {
        assert(false);
        return false;
    }
}

// TODO full tag poly support
using projection_results = std::map<Poly, InvarianceType>;

void insert_projection_result(const Poly& respoly, InvarianceType type, projection_results& results) {
    assert(!carl::is_zero(respoly));
    if (carl::is_constant(respoly)) return;
    for (const auto& f : carl::irreducibleFactors(respoly, false)) {
        if (!cad::projection::doesNotVanish(f)) {
            auto entry = results.find(f);
            if (entry != results.end()) {
                if (entry->second == InvarianceType::SIGN_INV && type == InvarianceType::ORD_INV) {
                    entry->second = InvarianceType::ORD_INV;
                }
            } else {
                results.emplace(f, type);
            }
        }
    }
}

void required_coefficients(const Poly& mpoly, const Model& model, carl::Variable variable, projection_results& results) {
    // TODO adapt Brown's version
    auto poly = carl::to_univariate_polynomial(mpoly, variable);
    while(!carl::is_zero(poly)) {
        smtrat::Poly lcpoly = smtrat::Poly(carl::to_univariate_polynomial(poly.lcoeff(), variable));
        if (!carl::is_zero(lcpoly)) {
            insert_projection_result(lcpoly, InvarianceType::SIGN_INV, results);
        }

        if (cad::projection::doesNotVanish(lcpoly)) break;
        auto mv = carl::model::evaluate(ConstraintT(lcpoly, carl::Relation::NEQ), model);
        assert(mv.isBool());
        if (mv.asBool()) break;

        poly.truncate();
    }
}

void project(const sector& cell, const Model& model, carl::Variable variable, projection_results& results) {
    // TODO try out different projection schemes (e.g. multiple endpoints)
    for (const auto& l : cell.lower_level) results.emplace(l, InvarianceType::ORD_INV);
    
    for (const auto& poly : cell.current_level) {
        { // discriminant
            auto respoly = Poly(carl::discriminant(carl::to_univariate_polynomial(poly, variable)));
            insert_projection_result(respoly, InvarianceType::ORD_INV, results);
        }
        required_coefficients(poly, model, variable, results);
    }

    // resultants
    if (cell.left_defining_poly) {
        auto u_left_defining_poly = carl::to_univariate_polynomial(cell.left_defining_poly->poly, variable);
        for (const auto& poly : cell.others_left) {
            auto respoly = Poly(carl::resultant(carl::to_univariate_polynomial(poly, variable), u_left_defining_poly));
            insert_projection_result(respoly, InvarianceType::ORD_INV, results);
        }
    }
    if (cell.right_defining_poly) {
        auto u_right_defining_poly = carl::to_univariate_polynomial(cell.right_defining_poly->poly, variable);
        for (const auto& poly : cell.others_right) {
            auto respoly = Poly(carl::resultant(carl::to_univariate_polynomial(poly, variable), u_right_defining_poly));
            insert_projection_result(respoly, InvarianceType::ORD_INV, results);
        }
    }
}

void project(const section& cell, const Model& model, carl::Variable variable, projection_results& results) {
    // TODO adapt Brown's version
    for (const auto& l : cell.lower_level) results.emplace(l, InvarianceType::ORD_INV);
    
    for (const auto& poly : cell.current_level) {
        // discriminant
        {
            auto respoly = Poly(carl::discriminant(carl::to_univariate_polynomial(poly, variable)));
            insert_projection_result(respoly, InvarianceType::ORD_INV, results);
        }
        required_coefficients(poly, model, variable, results);
    }

    // resultants
    auto u_point_defining_poly = carl::to_univariate_polynomial(cell.point_defining_poly.poly, variable);
    for (const auto& poly : cell.others) {
        auto respoly = Poly(carl::resultant(carl::to_univariate_polynomial(poly, variable), u_point_defining_poly));
        insert_projection_result(respoly, InvarianceType::ORD_INV, results);
    }
}

void project(const cell_at_level& cell, const Model& model, carl::Variable variable, projection_results& results) {
    if (std::holds_alternative<sector>(cell)) {
        project(std::get<sector>(cell), model, variable, results);
    } else {
        project(std::get<section>(cell), model, variable, results);
    }
}


struct covering_at_level {
    std::vector<cell_at_level> cells;
};
std::ostream& operator<<(std::ostream& os, const covering_at_level& data) {
    os << data.cells;
    return os;
}

void project(const covering_at_level& covering, const Model& model, carl::Variable variable, projection_results& results) {
    for (const auto& cell : covering.cells) {
        project(cell, model, variable, results);
    }

    for (size_t i = 0; i < covering.cells.size() - 1; i++) {
        const Poly& right_i = std::holds_alternative<sector>(covering.cells[i]) ? std::get<sector>(covering.cells[i]).right_defining_poly->poly : std::get<section>(covering.cells[i]).point_defining_poly.poly;
        const Poly& left_ip1 = std::holds_alternative<sector>(covering.cells[i+1]) ? std::get<sector>(covering.cells[i+1]).left_defining_poly->poly : std::get<section>(covering.cells[i+1]).point_defining_poly.poly;

        if (right_i.normalize() != left_ip1.normalize()) {
            auto respoly = Poly(carl::resultant(carl::to_univariate_polynomial(right_i, variable), carl::to_univariate_polynomial(left_ip1, variable)));
            insert_projection_result(respoly, InvarianceType::ORD_INV, results);
        }
    }
}

/*
carl::covering::TypedSetCover<const cell_at_level&> get_set_cover(const std::vector<cell_at_level>& cells) {
    std::vector<const cell_at_level&> sorted_cells;
    for (const auto& cell : cells) sorted_cells.emplace_back(cell);
    std::sort(sorted_cells.begin(), sorted_cells.end(), [](const auto& cell1, const auto& cell2) {
        if (std::holds_alternative<sector>(cell1) && !std::get<sector>(cell1).left) {
            return true;
        }
        if (std::holds_alternative<sector>(cell2) && !std::get<sector>(cell2).left) {
            return false;
        }

        const Poly& bound1 = std::holds_alternative<sector>(cell1) ? std::get<sector>(cell1).left : std::get<section>(cell2).point;
        const Poly& bound1 = std::holds_alternative<sector>(cell1) ? std::get<sector>(cell1).left : std::get<section>(cell2).point;

    });
}
*/

covering_at_level compute_covering(const std::vector<cell_at_level>& cells) {
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Compute unsat covering using " << cells);
    /*
    auto set_cover = get_set_cover(cells).get_cover([](auto& sc) {
        carl::Bitset res;
        res |= carl::covering::heuristic::remove_duplicates(sc);
        res |= carl::covering::heuristic::select_essential(sc);
        res |= carl::covering::heuristic::greedy(sc);
        // TODO sort by lower bound
        // TODO make sure that there are no redundancies
        return res;
    });
    
    covering_at_level covering;
    for (const auto& set : set_cover) {
        covering.cells.emplace_back(std::move(set));
    } 
    return covering;
    */

    covering_at_level covering;

    std::vector<const cell_at_level*> sorted_cells;
    for (const auto& cell : cells) sorted_cells.emplace_back(&cell);
    std::sort(sorted_cells.begin(), sorted_cells.end(), [](const cell_at_level* p_cell1, const cell_at_level* p_cell2) { // cell1 < cell2
        const auto& cell1 = *p_cell1;
        const auto& cell2 = *p_cell2;
        bool cell1_has_left = !(std::holds_alternative<sector>(cell1) && !std::get<sector>(cell1).left);
        bool cell1_has_right = !(std::holds_alternative<sector>(cell1) && !std::get<sector>(cell1).right);
        bool cell2_has_left = !(std::holds_alternative<sector>(cell2) && !std::get<sector>(cell2).left);
        bool cell2_has_right = !(std::holds_alternative<sector>(cell2) && !std::get<sector>(cell2).right);

        if (std::holds_alternative<section>(cell1) && std::holds_alternative<section>(cell2)) {
            return std::get<section>(cell1).point < std::get<section>(cell2).point;
        } else if (std::holds_alternative<sector>(cell1) && std::holds_alternative<section>(cell2)) {
            if (!cell1_has_left) return true;
            else {
                return std::get<sector>(cell1).left < std::get<section>(cell2).point;
            }
        } else if (std::holds_alternative<section>(cell1) && std::holds_alternative<sector>(cell2)) {
            if (!cell2_has_left) return false;
            else {
                return std::get<section>(cell1).point <= std::get<sector>(cell2).left;
            }
        } else if (std::holds_alternative<sector>(cell1) && std::holds_alternative<sector>(cell2)) {
            if (!cell1_has_left && cell2_has_left) {
                return true;
            } else if (!cell2_has_left && cell1_has_left)  {
                return false;
            } else if ((!cell1_has_left && !cell2_has_left) || (cell1_has_left && cell2_has_left && std::get<sector>(cell1).left == std::get<sector>(cell2).left) ) {
                if (!cell1_has_right && cell2_has_right) {
                    return false;
                } else if (!cell2_has_right && cell1_has_right)  {
                    return true;
                } else if (!cell2_has_right && !cell1_has_right) {
                    return false;
                } else  {
                    assert(cell2_has_right && cell1_has_right);
                    return std::get<sector>(cell1).right < std::get<sector>(cell2).right;
                }
            } else {
                assert(cell1_has_left && cell2_has_left);
                return std::get<sector>(cell1).left < std::get<sector>(cell2).left;
            }
        }
        assert(false);
        return false;
    });

    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Sorted cells " << sorted_cells);

    auto iter = sorted_cells.begin();
    assert(std::holds_alternative<sector>(**iter) && !std::get<sector>(**iter).left);
    while (iter+1 != sorted_cells.end() && std::holds_alternative<sector>(**(iter+1)) && !std::get<sector>(**(iter+1)).left) {
        SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Section " << **iter << " is redundant");
        iter++;
    }
    covering.cells.push_back(**iter);
    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Chose first section " << **iter);
    std::optional<RAN> current_right = std::get<sector>(**iter).right;
    iter++;
    while (current_right) {
        assert(iter != sorted_cells.end());
        if (std::holds_alternative<sector>(**iter)) {
            std::optional<RAN> current_left = *std::get<sector>(**iter).left;
            while (iter+1 != sorted_cells.end() && std::holds_alternative<sector>(**(iter+1)) && std::get<sector>(**(iter+1)).left == current_left) {
                SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Section " << **iter << " is redundant");
                iter++;
            }
            if (!std::get<sector>(**(iter)).right || *std::get<sector>(**(iter)).right > *current_right) {
                covering.cells.push_back(**iter);
                current_right = std::get<sector>(**(iter)).right;
                SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Choose section " << **iter);
                iter++;
            } else {
                SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Section " << **iter << " is redundant");
                iter++;
            }
        } else {
            assert(std::holds_alternative<section>(**iter));
            if (std::get<section>(**iter).point < *current_right) {
                SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Sector " << **iter << " is redundant");
                iter++;
            } else {
                assert(std::get<section>(**iter).point == *current_right);
                covering.cells.push_back(**iter);
                SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Chose sector " << **iter);
                iter++;
                while (std::holds_alternative<section>(**iter)) {
                    SMTRAT_LOG_TRACE("smtrat.mcsat.onecellcad.firstlevel", "Sector " << **iter << " is redundant");
                    iter++;
                }
            }
        }
    }
    
    return covering;
}

std::optional<std::vector<TagPoly>> first_level_projection(const FormulasT& input, const Model& model, carl::Variable variable) {
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecellcad.firstlevel", "First level projection with constraints = " << input << ", model = " << model << ", variable = " << variable);
    std::vector<cell_at_level> cells;
    for (const auto& f : input) {
        bool res = compute_unsat_intervals(f, model, variable, cells);
        if (!res) return std::nullopt;
    }
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecellcad.firstlevel", "Computed unsat intervals " << cells);
    auto covering = compute_covering(std::move(cells));
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecellcad.firstlevel", "Computed covering " << covering);
    projection_results results;
    project(covering, model, variable, results);
    std::vector<TagPoly> result_vector;
    for (const auto& [key, value] : results) result_vector.emplace_back(TagPoly { value, std::move(key) });
    SMTRAT_LOG_DEBUG("smtrat.mcsat.onecellcad.firstlevel", "Got projection " << result_vector);
    return result_vector;
}

}
}
}
} // namespace smtrat 