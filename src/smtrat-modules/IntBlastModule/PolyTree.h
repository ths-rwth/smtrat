/**
 * @file PolyTree.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 */

#pragma once

#include <optional>
#include <smtrat-common/smtrat-common.h>

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
            carl::Variable mVariable;
            Integer mConstant;
        };
        std::optional<PolyTree> mLeft;
        std::optional<PolyTree> mRight;

    public:
        PolyTreeContent(const Poly& _poly, PolyTree::Type _type, const PolyTree& _left, const PolyTree& _right) :
        mPoly(_poly), mType(_type), mVariable(), mLeft(_left), mRight(_right)
        {
            assert(_type == PolyTree::Type::SUM || _type == PolyTree::Type::PRODUCT);
        }

        PolyTreeContent(carl::Variable::Arg _variable) :
        mPoly(_variable), mType(PolyTree::Type::VARIABLE), mVariable(_variable), mLeft(), mRight()
        { }

        PolyTreeContent(Integer _constant) :
        mPoly(_constant), mType(PolyTree::Type::CONSTANT), mConstant(_constant), mLeft(), mRight()
        { }

        ~PolyTreeContent()
        {
            if(mType == PolyTree::Type::CONSTANT) {
                mConstant.~Integer();
            } else {
                mVariable.~Variable();
            }
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
