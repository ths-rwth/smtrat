#include "Simplification.h"

namespace smtrat::covering_ng {

void simplify(ParameterTree& tree) {
    assert(tree.status == 2 || tree.children.empty());

    if (tree.status == 2) {
        for (auto& child : tree.children) {
            simplify(child);
        }

        std::vector<ParameterTree> new_children;
        auto start = tree.children.begin();
        auto end = tree.children.begin();
        while(start != tree.children.end()) {
            while(start->status == 2 && start != tree.children.end()) {
                new_children.emplace_back(std::move(*start));
                start++;
            }
            end = start;
            if (start == tree.children.end()) break;

            while(start->status == end->status && end != tree.children.end()) {
                end++;
            }
            if (start+1 == end) {
                new_children.emplace_back(std::move(*start));
            } else {
                cadcells::datastructures::SymbolicInterval new_interval(start->interval->lower(), (end-1)->interval->upper());
                new_children.emplace_back(start->status, *start->variable, new_interval, !start->interval->is_section() ? *start->sample : *(start+1)->sample);
            }
            start = end;
        }
        tree.children = new_children;

        if (tree.children.size() == 1) { // optional, does not affect output formula
            //assert(tree.children.begin()->interval->lower().is_infty() && tree.children.begin()->interval->upper().is_infty());
            tree.status = tree.children.begin()->status;
            tree.children = tree.children.begin()->children;
        }
    }
}

}