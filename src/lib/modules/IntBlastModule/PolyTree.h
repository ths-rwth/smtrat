/**
 * @file PolyTree.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 */

#pragma once

#include <boost/optional.hpp>
#include "../../Common.h"

namespace smtrat
{
    // forward declaration
    class PolyTreeContent;

    // forward declaration
    class PolyTreePool;

    class PolyTree
    {
    private:
        const PolyTreeContent* mpContent;

    public:
        enum class Type : unsigned { VARIABLE, CONSTANT, SUM, PRODUCT };

        PolyTree(const Poly& _poly);

        const PolyTree& left() const;
        const PolyTree& right() const;
        carl::Variable::Arg variable() const;
        const Integer& constant() const;
        Type type() const;
        const Poly& poly() const;
    };

    class PolyTreeContent
    {
        friend class PolyTree;

    private:
        Poly mPoly;
        PolyTree::Type mType;
        union
        {
#ifdef __VS
            carl::Variable* mpVariableVS;
            Integer* mpConstantVS;
#else
			carl::Variable mVariable;
			Integer mConstant;
#endif
        };
        boost::optional<PolyTree> mLeft;
        boost::optional<PolyTree> mRight;

    public:
        PolyTreeContent(const Poly& _poly, PolyTree::Type _type, const PolyTree& _left, const PolyTree& _right) :
#ifdef __VS
        mPoly(_poly), mType(_type), mLeft(_left), mRight(_right)
		{
			mpVariableVS = new carl::Variable();
			assert(_type == PolyTree::Type::SUM || _type == PolyTree::Type::PRODUCT);
		}
#else
		mPoly(_poly), mType(_type), mVariable(), mLeft(_left), mRight(_right)
		{
			assert(_type == PolyTree::Type::SUM || _type == PolyTree::Type::PRODUCT);
		}
#endif

        PolyTreeContent(carl::Variable::Arg _variable) :
#ifdef __VS
        mPoly(_variable), mType(PolyTree::Type::VARIABLE), mLeft(), mRight()
        {
			mpVariableVS = new carl::Variable(_variable);
		}
#else
		mPoly(_variable), mType(PolyTree::Type::VARIABLE), mVariable(_variable), mLeft(), mRight()
		{ }
#endif

		PolyTreeContent(Integer _constant) :
#ifdef __VS
		mPoly(_constant), mType(PolyTree::Type::CONSTANT), mLeft(), mRight()
		{
			mpConstantVS = new Integer(_constant);
		}
#else
		mPoly(_constant), mType(PolyTree::Type::CONSTANT), mConstant(_constant), mLeft(), mRight()
		{ }
#endif

        ~PolyTreeContent()
        {
#ifdef __VS
            if(mType == PolyTree::Type::CONSTANT) {
                mpConstantVS->~Integer();
				delete mpConstantVS;
            } else {
                mpVariableVS->~Variable();
				delete mpVariableVS;
            }
#else
			if (mType == PolyTree::Type::CONSTANT) {
				mConstant.~Integer();
			}
			else {
				mVariable.~Variable();
			}
#endif
        }

        const Poly& poly() const
        {
            return mPoly;
        }

        bool operator==(const PolyTreeContent& _other) const
        {
            return mPoly == _other.mPoly;
        }

    };
} // namespace smtrat
