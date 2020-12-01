#pragma once

namespace smtrat::cadcells::realroots {

std::vector<indexed_root> section(poly_pool& pool, projections& proj, const Model& sample, const std::vector<poly_ref>& polys) {
    std::vector<indexed_root> results;
    for (const auto poly : polys) {
        if (proj.is_zero(sample, poly)) {
            auto roots = proj.real_roots(sample, poly);
            for (size_t idx = 0; idx < roots.size(); idx++) {
                if (root == sample.at(proj.main_var(poly))) {
                    results.emplace_back(poly, idx);
                    break;
                }
            }
        }
    }
    return results;
}

class root_ordering {

};

std::pair<std::vector<indexed_root>,std::vector<indexed_root>> sector(poly_pool& pool, projections& proj, const Model& sample, const std::vector<indexed_root>& polys) {

}



} 