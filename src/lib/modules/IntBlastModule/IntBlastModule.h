/**
 * @file IntBlastModule.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-05-12
 * Created on 2015-05-12.
 */

#pragma once

#include "../../solver/Module.h"
#include "../ICPModule/ICPModule.h"
#include "../../datastructures/VariableBounds.h"
#include "IntBlastStatistics.h"
#include "BVSolver.h"

namespace smtrat
{
    class BlastedType
    {
    private:
        std::size_t mWidth;
        bool mSigned;
        Integer mOffset;
        carl::Interval<Integer> mBounds;

    public:
        BlastedType() :
        mWidth(0), mSigned(false), mBounds(0, 0)
        {}

        BlastedType(std::size_t _width, bool _signed, Integer _offset = 0) :
        mWidth(_width), mSigned(_signed), mOffset(_offset),
        mBounds(_offset + (_signed ? -carl::pow(2, _width-1) : 0), _offset + (_signed ? carl::pow(2, _width-1)-1 : carl::pow(2, _width) -1))
        {}

        std::size_t width() const {
            return mWidth;
        }

        bool isSigned() const {
            return mSigned;
        }

        bool isConstant() const {
            return mBounds.lower() == mBounds.upper();
        }

        bool hasOffset() const {
            return ! carl::isZero(mOffset);
        }

        BlastedType withOffset(Integer _newOffset) const {
            return BlastedType(mWidth, mSigned, _newOffset);
        }

        BlastedType withWidth(std::size_t _width) const {
            return BlastedType(_width, mSigned, mOffset);
        }

        const Integer& offset() const {
            return mOffset;
        }

        const carl::Interval<Integer>& bounds() const {
            return mBounds;
        }

        const Integer& lowerBound() const {
            return mBounds.lower();
        }

        const Integer& upperBound() const {
            return mBounds.upper();
        }

        static BlastedType forSum(BlastedType _summand1, BlastedType _summand2) {
            std::size_t safeWidth1 = _summand1.width();
            std::size_t safeWidth2 = _summand2.width();
            bool makeSigned = (_summand1.isSigned() || _summand2.isSigned());

            if(_summand1.isSigned() != _summand2.isSigned()) {
                if(_summand1.isSigned()) {
                    ++safeWidth2;
                } else {
                    ++safeWidth1;
                }
            }

            std::size_t width = ((safeWidth1 > safeWidth2) ? safeWidth2 : safeWidth1) + 1;
            return BlastedType(width, makeSigned, _summand1.offset() + _summand2.offset());
        }

        static BlastedType forProduct(BlastedType _factor1, BlastedType _factor2) {
            assert(! _factor1.hasOffset() && ! _factor2.hasOffset());
            bool makeSigned = _factor1.isSigned() || _factor2.isSigned();
            std::size_t width = _factor1.width() + _factor2.width() - (_factor1.isSigned() && _factor2.isSigned() ? 1 : 0);
            return BlastedType(width, makeSigned);
        }

        friend std::ostream& operator<<( std::ostream& _out, const BlastedType& _type ) {
            return (_out << "[" << (_type.mSigned ? "s" : "u") << _type.mWidth << "]");
        }
    };

    class BlastedTerm
    {
    private:
        BlastedType mType;
        carl::BVTerm mTerm;

    public:
        BlastedTerm() :
        mType(), mTerm()
        {}

        BlastedTerm(const BlastedType& _type, const carl::BVTerm& _term) :
        mType(_type), mTerm(_term)
        {
            assert(_type.width() == _term.width());
        }

        BlastedTerm(std::size_t _width, bool _signed, Integer _offset = 0) :
        BlastedTerm(BlastedType(_width, _signed, _offset))
        { }

        BlastedTerm(const BlastedType& _type) :
        mType(_type), mTerm()
        {
            carl::Variable var = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_BITVECTOR);
            carl::Sort bvSort = carl::SortManager::getInstance().getSort("BitVec", {_type.width()});
            carl::BVVariable bvVar(var, bvSort);
            mTerm = carl::BVTerm(carl::BVTermType::VARIABLE, bvVar);
        }

        const BlastedType& type() const {
            return mType;
        }

        const carl::BVTerm& term() const {
            return mTerm;
        }

        const carl::BVTerm& operator()() const {
            return mTerm;
        }

        friend std::ostream& operator<<( std::ostream& _out, const BlastedTerm& _term ) {
            return (_out << _term.mTerm << " " << _term.mType);
        }
    };

    class BlastedPoly
    {
    private:
        bool mIsConstant;
        Integer mConstant;
        BlastedTerm mTerm;
        FormulasT mConstraints;

    public:
        BlastedPoly() :
        mIsConstant(true), mConstant(), mTerm(), mConstraints()
        { }

        BlastedPoly(Integer _constant) :
        mIsConstant(true), mConstant(_constant), mTerm(), mConstraints()
        { }

        BlastedPoly(Integer _constant, FormulasT _constraints) :
        mIsConstant(true), mConstant(_constant), mTerm(), mConstraints(_constraints)
        { }

        BlastedPoly(BlastedTerm _term) :
        mIsConstant(false), mConstant(), mTerm(_term), mConstraints()
        { }

        BlastedPoly(BlastedTerm _term, FormulasT _constraints) :
        mIsConstant(false), mConstant(), mTerm(_term), mConstraints(_constraints)
        { }

        bool isConstant() const {
            return mIsConstant;
        }

        const Integer& constant() const {
            assert(mIsConstant);
            return mConstant;
        }

        const BlastedTerm& term() const {
            assert(! mIsConstant);
            return mTerm;
        }

        const FormulasT& constraints() const {
            assert(! mIsConstant);
            return mConstraints;
        }

        const Integer& lowerBound() const {
            if(mIsConstant) {
                return mConstant;
            } else {
                return mTerm.type().lowerBound();
            }
        }

        const Integer& upperBound() const {
            if(mIsConstant) {
                return mConstant;
            } else {
                return mTerm.type().upperBound();
            }
        }

        friend std::ostream& operator<<( std::ostream& _out, const BlastedPoly& _poly ) {
            if(_poly.isConstant()) {
                return (_out << carl::toString(_poly.constant(), false) << " (const)");
            } else {
                return (_out << _poly.term());
            }
        }
    };

    class BlastedConstr
    {
    private:
        FormulaT mFormula;
        FormulasT mConstraints;

    public:
        BlastedConstr() : mFormula(), mConstraints()
        { }

        BlastedConstr(const FormulaT& _formula, const FormulasT& _constraints) :
        mFormula(_formula), mConstraints(_constraints)
        { }

        BlastedConstr(const FormulaT& _formula) :
        mFormula(_formula), mConstraints()
        { }

        BlastedConstr(bool _satisfied) :
        BlastedConstr(FormulaT(_satisfied ? carl::FormulaType::TRUE : carl::FormulaType::FALSE))
        { }

        const FormulaT& formula() const {
            return mFormula;
        }

        const FormulasT& constraints() const {
            return mConstraints;
        }

        friend std::ostream& operator<<( std::ostream& _out, const BlastedConstr& _constr ) {
            return (_out << _constr.formula() << " (&" << _constr.constraints().size() << "cs)");
        }
    };

    class PolyTree
    {
    public:
        enum class Type : unsigned { VARIABLE, CONSTANT, SUM, PRODUCT };

    private:
        // TODO: Union
        Type mType;
        carl::Variable mVariable;
        Integer mConstant;
        const PolyTree* mLeft;
        const PolyTree* mRight;
        Poly mPoly;

    public:
        PolyTree( const Poly& _poly ) : mType(Type::VARIABLE), mVariable(), mConstant(), mLeft(nullptr), mRight(nullptr), mPoly(_poly) {
            Poly poly(_poly);
            poly.makeOrdered();

            std::size_t nrTerms = poly.nrTerms();

            if(nrTerms == 0) {
                mType = Type::CONSTANT;
                mConstant = 0;
                return;
            }
            if(nrTerms > 1) {
                auto lastTerm = poly.rbegin();
                mType = Type::SUM;
                mLeft = new PolyTree(poly - *lastTerm);
                mRight = new PolyTree(Poly(*lastTerm));
                return;
            }

            const TermT& term = poly[0];
            Rational coeff = term.coeff();

            if(term.isConstant()) {
                mType = Type::CONSTANT;
                mConstant = coeff;
                return;
            }

            const carl::Monomial::Arg monomial = term.monomial();

            if(! carl::isOne(coeff)) {
                mType = Type::PRODUCT;
                mLeft = new PolyTree(Poly(coeff));
                mRight = new PolyTree(Poly(monomial));
                return;
            }

            auto variableAndExponent = *(monomial->begin());

            if(monomial->nrVariables() > 1) {
                carl::Monomial::Arg head = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second);
                carl::Monomial::Arg tail = monomial->dropVariable(variableAndExponent.first);
                mType = Type::PRODUCT;
                mLeft = new PolyTree(Poly(head));
                mRight = new PolyTree(Poly(tail));
                return;
            }

            if(variableAndExponent.second > 1) {
                carl::Monomial::Arg remainder = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second - 1);
                mType = Type::PRODUCT;
                mLeft = new PolyTree(Poly(remainder));
                mRight = new PolyTree(Poly(variableAndExponent.first));
                return;
            }

            mType = Type::VARIABLE;
            mVariable = variableAndExponent.first;
        }

        ~PolyTree() {
            delete mLeft;
            delete mRight;
        }

        const PolyTree& left() const {
            assert(mLeft != nullptr);
            return *mLeft;
        }

        const PolyTree& right() const {
            assert(mRight != nullptr);
            return *mRight;
        }

        carl::Variable::Arg variable() const {
            assert(mType == Type::VARIABLE);
            return mVariable;
        }

        const Integer& constant() const {
            assert(mType == Type::CONSTANT);
            return mConstant;
        }

        Type type() const {
            return mType;
        }

        const Poly& poly() const {
            return mPoly;
        }
    };

    class ConstrTree
    {
    private:
        carl::Relation mRelation;
        PolyTree* mpLeftPoly;
        PolyTree* mpRightPoly;
        ConstraintT mConstraint;

    public:
        ConstrTree(const ConstraintT& _constraint) :
        mRelation(_constraint.relation()), mpLeftPoly(nullptr), mpRightPoly(nullptr), mConstraint(_constraint)
        {
            Poly rightPoly(- _constraint.constantPart());
            Poly leftPoly(_constraint.lhs() - _constraint.constantPart());

            mpLeftPoly = new PolyTree(leftPoly);
            mpRightPoly = new PolyTree(rightPoly);
        }

        ~ConstrTree() {
            delete mpLeftPoly;
            delete mpRightPoly;
        }

        carl::Relation relation() const {
            return mRelation;
        }

        const PolyTree& left() const {
            return *mpLeftPoly;
        }

        const PolyTree& right() const {
            return *mpRightPoly;
        }

        const ConstraintT& constraint() const {
            return mConstraint;
        }
    };

    template<typename Element, typename Origin>
    class ElementWithOrigins
    {
        private:
            Element mElement;
            std::set<Origin> mOrigins;

        public:
            ElementWithOrigins(const Element& _element) :
            mElement(_element), mOrigins()
            { }

            ElementWithOrigins(const Element& _element, const Origin& _origin) :
            mElement(_element), mOrigins({ _origin })
            { }

            const Element& element() const {
                return mElement;
            }

            const std::list<Origin> origins() const {
                return mOrigins;
            }

            void addOrigin(const Origin& _origin) {
                mOrigins.insert(_origin);
            }

            bool removeOrigin(const Origin& _origin) {
                if(mOrigins.erase(_origin) == 1 && mOrigins.empty()) {
                    return true;
                }

                return false;
            }

            bool hasOrigins() {
                return ! mOrigins.empty();
            }
    };

    template<typename Element, typename Origin>
    class CollectionWithOrigins
    {
        private:
            typedef ElementWithOrigins<Element, Origin> ElementWO;
            typedef std::list<ElementWO> Super;

            Super mItems;
            carl::FastMap<Element, typename Super::iterator> mElementPositions;
            carl::FastMap<Origin, std::list<typename Super::iterator> > mOriginOccurings;
            std::set<Element> mElementsWithoutOrigins;

        public:
            typedef typename Super::iterator iterator;
            typedef typename Super::const_iterator const_iterator;

            CollectionWithOrigins() :
            mItems(), mElementPositions(), mOriginOccurings()
            { }

            bool contains(const Element& _element) {
                return mElementPositions.find(_element) != mElementPositions.end();
            }

            bool add(const Element& _element, const Origin& _origin) {
                auto lookup = mElementPositions.find(_element);

                if(lookup == mElementPositions.end()) {
                    ElementWO newElement(_element, _origin);
                    mItems.push_back(newElement);
                    auto inserted = std::prev(mItems.end());
                    mElementPositions[_element] = inserted;
                    mOriginOccurings[_origin].push_back(inserted);
                    return true;
                } else {
                    lookup->second->addOrigin(_origin);
                    mOriginOccurings[_origin].push_back(lookup->second);
                    return false;
                }
            }

            bool removeOrigin(const Origin& _origin) {
                auto originIt = mOriginOccurings.find(_origin);

                if(originIt != mOriginOccurings.end()) {
                    std::list<typename Super::iterator>& occurings = originIt->second;

                    for(auto& item : occurings) {
                        if(item->removeOrigin(_origin)) {
                            mElementsWithoutOrigins.insert(item->element());
                            mElementPositions.erase(item->element());
                            mItems.erase(item);
                        }
                    }
                    mOriginOccurings.erase(originIt);
                    return true;
                }
                return false;
            }

            bool removeOrigins(const std::set<Origin>& _origins) {
                bool removedAnything = false;

                for(auto& it = _origins.begin();it != _origins.end();++it) {
                    removedAnything = removedAnything || removeOrigin(*it);
                }

                return removedAnything;
            }

            iterator begin() {
                return mItems.begin();
            }

            iterator end() {
                return mItems.end();
            }

            const_iterator cbegin() const {
                return mItems.cbegin();
            }

            const_iterator cend() const {
                return mItems.cend();
            }

            const std::set<Element>& elementsWithoutOrigins() const {
                return mElementsWithoutOrigins;
            }

            void clearElementsWithoutOrigins() {
                mElementsWithoutOrigins.clear();
            }

    };


    class IntBlastModule : public Module
    {
        private:
            typedef smtrat::vb::VariableBounds<FormulaT> VariableBounds;
            typedef carl::Interval<Integer> IntegerInterval;
            enum class SolutionOrigin : unsigned { NONE, ICP, BV, BACKEND };

            VariableBounds mBoundsFromInput;
            VariableBounds mBoundsInRestriction;

            CollectionWithOrigins<carl::Variable, FormulaT> mInputVariables;
            CollectionWithOrigins<carl::Variable, FormulaT> mNonlinearInputVariables;

            ModuleInput* mpICPInput; // ReceivedFormula of the internal ICP Module
            std::vector<std::atomic_bool*> mICPFoundAnswer;
            RuntimeSettings* mpICPRuntimeSettings;
            ICPModule mICP;
            FormulaT mConstraintFromBounds;
            FormulasT mProcessedFormulasFromICP;

            ModuleInput* mpBVInput; // Input of the internal BV solver
            BVSolver* mpBVSolver;
            std::list<FormulaT> mFormulasToEncode;

            FormulaT mOutsideRestriction;
            const FormulaT mOutsideRestrictionOrigin;

            SolutionOrigin mSolutionOrigin;

            std::map<Poly, BlastedPoly> mPolyBlastings; // Map from polynomials to bit-vector terms representing them in the blasted output
            std::map<ConstraintT, BlastedConstr> mConstrBlastings;
            std::map<Poly, carl::Variable> mSubstitutes; // Map from polynomials to integer variables representing them in the ICP input
            CollectionWithOrigins<Poly, FormulaT> mSubstitutedPolys;

        public:
            IntBlastModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings* _settings, Conditionals& _conditionals, Manager* _manager = NULL );

            ~IntBlastModule();

            // Main interfaces.

            /**
             * Informs the module about the given constraint. It should be tried to inform this
             * module about any constraint it could receive eventually before assertSubformula
             * is called (preferably for the first time, but at least before adding a formula
             * containing that constraint).
             * @param _constraint The constraint to inform about.
             * @return false, if it can be easily decided whether the given constraint is inconsistent;
             *          true, otherwise.
             */
            bool informCore( const FormulaT& _constraint );

            /**
             * Informs all backends about the so far encountered constraints, which have not yet been communicated.
             * This method must not and will not be called more than once and only before the first runBackends call.
             */
	        void init();

            /**
             * The module has to take the given sub-formula of the received formula into account.
             *
             * @param _subformula The sub-formula to take additionally into account.
             * @return false, if it can be easily decided that this sub-formula causes a conflict with
             *          the already considered sub-formulas;
             *          true, otherwise.
             */
            bool addCore( ModuleInput::const_iterator _subformula );

            /**
             * Removes the subformula of the received formula at the given position to the considered ones of this module.
             * Note that this includes every stored calculation which depended on this subformula, but should keep the other
             * stored calculation, if possible, untouched.
             *
             * @param _subformula The position of the subformula to remove.
             */
            void removeCore( ModuleInput::const_iterator _subformula );

            /**
             * Updates the current assignment into the model.
             * Note, that this is a unique but possibly symbolic assignment maybe containing newly introduced variables.
             */
            void updateModel() const;

            /**
             * Checks the received formula for consistency.
             * @param _full false, if this module should avoid too expensive procedures and rather return unknown instead.
             * @return True,    if the received formula is satisfiable;
             *         False,   if the received formula is not satisfiable;
             *         Unknown, otherwise.
             */
            Answer checkCore( bool _full );

    private:

            BlastedPoly blastSum(const BlastedPoly& _summand1, const BlastedPoly& _summand2);
            BlastedPoly blastProduct(const BlastedPoly& _factor1, const BlastedPoly& _factor2);
            bool reblastingNeeded(const BlastedPoly& _previousBlasting, const IntegerInterval& _interval, bool _linear) const;
            void unblastVariable(const carl::Variable& _variable);
            void blastVariable(const carl::Variable& _variable, const IntegerInterval& _interval, bool _allowOffset);
            std::size_t chooseWidth(const Integer& _numberToCover, std::size_t _maxWidth, bool _signed) const;
            void updateBoundsFromICP();
            void updateOutsideRestrictionConstraint(bool _includeSubstitutes);
            void addFormulaToICP(const FormulaT& _formula, const FormulaT& _origin);
            void addConstraintToICP(FormulaT _formula);
            void removeFormulaFromICP(const FormulaT& _formula, const FormulaT& _origin);
            void removeOriginFromICP(const FormulaT& _origin);
            void removeOriginFromBV(const FormulaT& _origin);
            void updateModelFromICP() const;
            void updateModelFromBV() const;
            carl::BVTerm encodeBVConstant(const Integer& _constant, const BlastedType& _type) const;
            Integer decodeBVConstant(const carl::BVValue& _value, const BlastedType& _type) const;
            carl::BVTerm resizeBVTerm(const BlastedTerm& _term, std::size_t _width) const;
            BlastedPoly reduceToRange(const BlastedPoly& _input, const IntegerInterval& _interval) const;
            bool evaluateRelation(carl::Relation _relation, const Integer& _first, const Integer& _second) const;
            FormulasT blastConstraint(const ConstraintT& _constraint);
            const BlastedPoly& blastPolyTree(const PolyTree& _poly, FormulasT& _collectedFormulas);
            const BlastedConstr& blastConstrTree(const ConstrTree& _constraint, FormulasT& _collectedFormulas);
            void addBoundRestrictionsToICP(carl::Variable _variable, const BlastedType& blastedType);
            void removeBoundRestrictionsFromICP(carl::Variable _variable);
            IntegerInterval getNum(const RationalInterval& _interval) const;
    };
}
