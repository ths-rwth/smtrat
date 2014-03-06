/** 
 * @file   Relation.h
 * @author Sebastian Junges
 *
 */

#pragma once

namespace smtrat
{
enum class Relation : unsigned { EQ = 0, NEQ = 1, LESS = 2, GREATER = 3, LEQ = 4, GEQ = 5 };

bool relationIsStrict(Relation r);
}
