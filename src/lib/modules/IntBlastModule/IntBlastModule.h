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
    class BlastingParameters
    {
    private:
        carl::BVVariable mVariable;
        bool mSigned;
        carl::Interval<Integer> mBounds;

    public:
        BlastingParameters() :
        mVariable(), mSigned(false), mBounds(0, 0)
        {}

        BlastingParameters( const carl::BVVariable& _variable, bool _signed ) :
        mVariable(_variable), mSigned(_signed),
        mBounds((_signed ? -carl::pow(2, _variable.width()-1) : 0), (_signed ? carl::pow(2, _variable.width()-1)-1 : carl::pow(2, width()) -1))
        {}

        const carl::BVVariable variable() const {
            return mVariable;
        }

        bool isSigned() const {
            return mSigned;
        }

        std::size_t width() const {
            return mVariable.width();
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

        static BlastingParameters createWithVariable(std::size_t _width, bool _signed)
        {
            carl::Variable var = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_BITVECTOR);
            carl::Sort bvSort = carl::SortManager::getInstance().getSort("BitVec", {_width});
            carl::BVVariable bvVar(var, bvSort);
            return BlastingParameters(bvVar, _signed);
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

            std::map<carl::Variable, BlastingParameters> mBlastingParameters; // Map from integer variables (substitutes or input variables) to bit-vector terms
            std::map<Poly, carl::Variable> mSubstitutes; // Map from polynomials to integer variables representing them in the ICP input
            // Members.

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
            void createSubstitutes(const TermT& _term);
            void createSubstitutes(const carl::Variable::Arg variable, carl::exponent exponent);
            bool createSubstitute(const Poly& _poly);
            // void createMonomialSubstitutes(const FormulaT& _formula);
            PolyDecomposition decompose(const Poly& _polynomial) const;
            void updateBlastingParameters();
            BlastingParameters chooseBlastingParameters(const DoubleInterval _interval, std::size_t _maxWidth = 0) const;
            void blastSubstitutes();
            void blastSum(const BlastingParameters& _summand1, const BlastingParameters& _summand2, const BlastingParameters& _sum);
            void blastProduct(const BlastingParameters& _factor1, const BlastingParameters& _factor2, const BlastingParameters& _product);
            void safeCast(const BlastingParameters& _from, const BlastingParameters& _to);

            void addSubformulaToICPFormula(const FormulaT& _formula, const FormulaT& _origin);


    };
}
