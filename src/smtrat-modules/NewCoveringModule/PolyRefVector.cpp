#include "PolyRefVector.h"

namespace smtrat {

void PolyRefVector::add(const smtrat::cadcells::datastructures::PolyRef& ref) {
    //Todo check if Poly is factorized?
	std::vector<smtrat::cadcells::datastructures::PolyRef>::emplace_back(ref);
};

void PolyRefVector::reduce(){
    std::sort(begin(), end());
    std::vector<smtrat::cadcells::datastructures::PolyRef>::erase(std::unique(begin(), end()), end());
}

void PolyRefVector::add(const PolyRefVector& refVector){
    for(const auto& item: refVector){
        add(item);
    }
}


} // namespace smtrat<