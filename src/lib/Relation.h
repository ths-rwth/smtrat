/** 
 * @file   Relation.h
 * @author Sebastian Junges
 *
 */

#pragma once

#include <iostream>

namespace smtrat
{
enum class Relation : unsigned { EQ = 0, NEQ = 1, LESS = 2, GREATER = 3, LEQ = 4, GEQ = 5 };
inline std::ostream& operator<<(std::ostream& os, const Relation& r) {
	switch (r) {
		case Relation::EQ:		os << "="; break;
		case Relation::NEQ:		os << "<>"; break;
		case Relation::LESS:	os << "<"; break;
		case Relation::GREATER: os << ">"; break;
		case Relation::LEQ:		os << "<="; break;
		case Relation::GEQ:		os << ">="; break;
	}
	return os;
}

inline bool relationIsStrict(Relation r)
{
	return r == Relation::LESS || r == Relation::GREATER || r == Relation::NEQ;
}
}
