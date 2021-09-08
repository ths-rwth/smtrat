#pragma once

#include <cstddef>
#include <vector>
#include <cassert>

#include <smtrat-cadcells/datastructures/polynomials.h>
#include <smtrat-cadcells/datastructures/projections.h>

namespace smtrat {

class PolyRefVector : public std::vector<smtrat::cadcells::datastructures::PolyRef> {

private:

	//disable unnecessary functions
	void emplace() {}

	void emplace_back() {}

	void insert() {}

	void push_back() {}

public:
	//Construct as empty vector
	PolyRefVector() {}

	PolyRefVector(std::initializer_list<smtrat::cadcells::datastructures::PolyRef> list) {
		for(const auto& polyRef : list){
			add(polyRef) ;
		}
	}

    //Add new PolyRef Todo: assert that the underlying polynomial is squareFree?
	void add(const smtrat::cadcells::datastructures::PolyRef& ref) ;

	void add(const PolyRefVector& refVector) ;

    //Sort and remove duplicates
    void reduce();

};

inline std::ostream& operator<<(std::ostream& os, const PolyRefVector& vec){
	os << "[" << vec.size() << " : " ;
	for(const auto& item: vec){
		os << item << ", " ;
	}
	os << "\b\b]" ;
	return os;
}


} // namespace smtrat