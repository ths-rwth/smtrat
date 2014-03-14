/** 
 * @file   Relation.h
 * @author Sebastian Junges
 *
 */

#pragma once

namespace smtrat
{
enum class Relation : unsigned { EQ = 0, NEQ = 1, LESS = 2, GREATER = 3, LEQ = 4, GEQ = 5 };

inline bool relationIsStrict(Relation r)
{
	return r == Relation::LESS || r == Relation::GREATER || r == Relation::NEQ;
}
}
