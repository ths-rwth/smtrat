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
        carl::Interval<Integer> mBounds;

    public:
        BlastedType() :
        mWidth(0), mSigned(false), mBounds(0, 0)
        {}

        BlastedType( std::size_t _width, bool _signed ) :
        mWidth(_width), mSigned(_signed),
        mBounds((_signed ? -carl::pow(2, _width-1) : 0), (_signed ? carl::pow(2, _width-1)-1 : carl::pow(2, _width) -1))
        {}

        std::size_t width() const {
            return mWidth;
        }

        bool isSigned() const {
            return mSigned;
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
            return BlastedType(width, makeSigned);
        }

        static BlastedType forProduct(BlastedType _factor1, BlastedType _factor2) {
            bool makeSigned = _factor1.isSigned() || _factor2.isSigned();
            std::size_t width = _factor1.width() + _factor2.width() - (_factor1.isSigned() && _factor2.isSigned() ? 1 : 0);
            return BlastedType(width, makeSigned);
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
    };

    class PolyDecomposition
    {
    public:
        enum class Type : unsigned { VARIABLE, CONSTANT, SUM, PRODUCT };

    private:
        Type mType;
        carl::Variable mVariable;
        Rational mConstant;
        Poly mLeft;
        Poly mRight;

    public:
        PolyDecomposition( Type _type, carl::Variable::Arg _variable ) :
        mType(_type), mVariable(_variable), mConstant(), mLeft(), mRight()
        {
            assert(_type == Type::VARIABLE);
        }

        PolyDecomposition( Type _type, const Rational& _constant ) :
        mType(_type), mVariable(), mConstant(_constant), mLeft(), mRight()
        {
            assert(_type == Type::CONSTANT);
        }

        PolyDecomposition( Type _type, const Poly& _left, const Poly& _right ) :
        mType(_type), mVariable(), mConstant(), mLeft(_left), mRight(_right)
        {
            assert(_type == Type::SUM || _type == Type::PRODUCT);
        }

        const Poly& left() {
            assert(mType == Type::SUM || mType == Type::PRODUCT);
            return mLeft;
        }

        const Poly& right() {
            assert(mType == Type::SUM || mType == Type::PRODUCT);
            return mRight;
        }

        carl::Variable::Arg variable() {
            assert(mType == Type::VARIABLE);
            return mVariable;
        }

        const Rational& constant() {
            assert(mType == Type::CONSTANT);
            return mConstant;
        }

        Type type() {
            return mType;
        }
    };


    class IntBlastModule : public Module
    {
        private:
            typedef smtrat::vb::VariableBounds<FormulaT> VariableBounds;

            VariableBounds mBoundsFromInput;
            VariableBounds mBoundsInRestriction;

            ModuleInput* mICPInput; // ReceivedFormula of the internal ICP Module
            std::vector<std::atomic_bool*> mICPFoundAnswer;
            RuntimeSettings* mICPRuntimeSettings;
            ICPModule mICP;
            FormulasT mProcessedFormulasFromICP;

            BVSolver* mBVSolver;
            bool mLastSolutionFoundByBlasting;

            std::map<Poly, BlastedTerm> mBlastings; // Map from polynomials to bit-vector terms representing them in the blasted output
            std::map<Poly, carl::Variable> mSubstitutes; // Map from polynomials to integer variables representing them in the ICP input

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
            void createSubstitutes(const FormulaT& _formula);
            void createSubstitutes(const Poly& _poly);
            bool createSubstitute(const Poly& _poly);
            // void createMonomialSubstitutes(const FormulaT& _formula);
            PolyDecomposition decompose(const Poly& _polynomial) const;
            void blastInputVariables();
            BlastedType chooseBlastedType(const DoubleInterval _interval, std::size_t _maxWidth = 0) const;
            void blastSubstitutes();
            const BlastedTerm& blastedTermForPolynomial(const Poly& _poly);
            void blastSum(const BlastedTerm& _summand1, const BlastedTerm& _summand2, const BlastedTerm& _sum);
            void blastProduct(const BlastedTerm& _factor1, const BlastedTerm& _factor2, const BlastedTerm& _product);
            void safeCast(const BlastedTerm& _from, const BlastedTerm& _to);

            void addSubformulaToICPFormula(const FormulaT& _formula, const FormulaT& _origin);


    };
}
