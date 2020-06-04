/**
 * @file IntBlastModule.tpp
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 */

#include "IntBlastModule.h"

#define INTBLAST_DEBUG_ENABLED 0
#define INTBLAST_DEBUG(x) do { \
  if (INTBLAST_DEBUG_ENABLED) { std::cout << "[IntBlast] " << x << std::endl; } \
} while (0)

namespace smtrat
{
    /**
     * Constructors.
     */

    template<class Settings>
    IntBlastModule<Settings>::IntBlastModule( const ModuleInput* _formula, Conditionals& _conditionals, Manager* _manager ):
    Module( _formula, _conditionals, _manager ),
    mBoundsFromInput(),
    mBoundsInRestriction(),
    mInputVariables(),
    mNonlinearInputVariables(),
    mpICPInput(new ModuleInput()),
    mICPFoundAnswer( std::vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
    mICP(mpICPInput, mICPFoundAnswer),
    mConstraintFromBounds(carl::freshBooleanVariable()),
    mProcessedFormulasFromICP(),
    mpBVInput(new ModuleInput()),
    mpBVSolver(new BVSolver()),
    mFormulasToEncode(),
    mSolutionOrigin(SolutionOrigin::NONE),
    mPolyBlastings(),
    mConstrBlastings(),
    mSubstitutes(),
    mPolyParents(),
    mShrunkPolys()
    {
        // TODO: Do we have to do some more initialization stuff here? Settings?
    }

    /**
     * Destructor.
     */

    template<class Settings>
    IntBlastModule<Settings>::~IntBlastModule()
    {
        delete mpICPInput;
        while( !mICPFoundAnswer.empty() )
        {
            std::atomic_bool* toDel = mICPFoundAnswer.back();
            mICPFoundAnswer.pop_back();
            delete toDel;
        }
        mICPFoundAnswer.clear();

        delete mpBVSolver;
        delete mpBVInput;
    };

    template<class Settings>
    bool IntBlastModule<Settings>::informCore( const FormulaT& _constraint )
    {
        informBackends(_constraint);
        return true;
    }

    template<class Settings>
    void IntBlastModule<Settings>::init()
    {}

    template<class Settings>
    bool IntBlastModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        const FormulaT& formula = _subformula->formula();
        INTBLAST_DEBUG("ADD " << formula);

        std::vector<ConstraintT> containedConstraints;
        formula.getConstraints(containedConstraints);

        /*
         * Steps that are applied for every constraint in formula
         */

        for(const ConstraintT& constraint : containedConstraints) {
            // Retrieve all arithmetic variables in formula
            carl::Variables variablesInFormula;
            carl::Variables nonlinearVariablesInFormula;
            const Poly& poly = constraint.lhs();
            formula.arithmeticVars(variablesInFormula);
            for(auto termIt = poly.begin();termIt != poly.end();++termIt) {
                if(termIt->getNrVariables() > 1 || ! termIt->isLinear()) {
                    termIt->gatherVariables(nonlinearVariablesInFormula);
                }
            }

            // Update 'mInputVariables' and 'mNonlinearInputVariables' sets
            for(auto& variable : variablesInFormula) {
                mInputVariables.add(variable, formula);
            }
            for(auto& variable : nonlinearVariablesInFormula) {
                mNonlinearInputVariables.add(variable, formula);
            }

            // Introduce substitutes in ICP
            if(Settings::apply_icp) {
                addSubstitutesToICP(constraint, formula);
            }

            // Update mPolyParents (child->parent relationship)
            addPolyParents(constraint);
        }

        /*
         * Steps that are applied if the formula is only a single constraint
         */

        if(formula.getType() == carl::FormulaType::CONSTRAINT) {
            // Update mBoundsFromInput using the new formula
            mBoundsFromInput.addBound(formula.constraint(), formula);

            // Pass global formula to ICP
            if(Settings::apply_icp) {
                addConstraintFormulaToICP(formula);
            }
        }

        /*
         * Steps that are applied for the whole formula
         */

        // Schedule formula for encoding to BV logic
        mFormulasToEncode.insert(formula);

        // Add new formula to backend
        addReceivedSubformulaToPassedFormula(_subformula);

        return ! mBoundsFromInput.isConflicting();
    }

    template<class Settings>
    void IntBlastModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        const FormulaT& formula = _subformula->formula();
        INTBLAST_DEBUG("REMOVE " << formula);

        mInputVariables.removeOrigin(formula);
        mNonlinearInputVariables.removeOrigin(formula);

        if(formula.getType() == carl::FormulaType::CONSTRAINT) {
            mBoundsFromInput.removeBound(formula.constraint(), formula);
        }
        // mBoundsInRestriction: updated by updateBoundsFromICP() in next check

        if(Settings::apply_icp) {
            removeOriginFromICP(formula);
        }
        removeOriginFromBV(formula);

        mFormulasToEncode.erase(formula);
    }

    template<class Settings>
    void IntBlastModule<Settings>::updateModel() const
    {
        mModel.clear();
        if(solverState() == SAT)
        {
            switch(mSolutionOrigin) {
                case SolutionOrigin::ICP:
                    updateModelFromICP();
                    break;
                case SolutionOrigin::BV:
                    updateModelFromBV();
                    break;
                case SolutionOrigin::BACKEND:
                    getBackendsModel();
                    break;
                default:
                    assert(false);
            }
        }
    }

    template<class Settings>
    carl::BVTerm IntBlastModule<Settings>::encodeBVConstant(const Integer& _constant, const BVAnnotation& _type) const
    {
        assert(_constant >= _type.lowerBound() && _constant <= _type.upperBound());
        carl::BVValue constValue(_type.width(), _constant - _type.offset());
        return carl::BVTerm(carl::BVTermType::CONSTANT, constValue);
    }

    template<class Settings>
    Integer IntBlastModule<Settings>::decodeBVConstant(const carl::BVValue& _value, const BVAnnotation& _type) const
    {
        Integer summand(1);
        Integer converted(0);

        // Unsigned conversion from binary to integer
        for(std::size_t position = 0;position<_value.width();++position) {
            if(_value[position]) {
                converted += summand;
            }
            summand *= Integer(2);
        }

        // For negative numbers in two's complement, subtract 2^width from result
        if(_type.isSigned() && _value[_value.width()-1]) {
            converted -= summand;
        }

        return converted + _type.offset();
    }

    template<class Settings>
    carl::BVTerm IntBlastModule<Settings>::resizeBVTerm(const AnnotatedBVTerm& _term, std::size_t _width) const
    {
        assert(_width >= _term.type().width());

        if(_width == _term.type().width()) {
            return _term.term();
        } else {
            carl::BVTermType ext = (_term.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U);
            return carl::BVTerm(ext, _term.term(), _width - _term.type().width());
        }
    }

    template<class Settings>
    BlastedPoly IntBlastModule<Settings>::blastSum(const BlastedPoly& _summand1, const BlastedPoly& _summand2)
    {
        if(_summand1.isConstant() && _summand2.isConstant()) {
            return BlastedPoly(_summand1.constant() + _summand2.constant());
        } else if(_summand1.isConstant() || _summand2.isConstant()) {
            const BlastedPoly& constantSummand = (_summand1.isConstant() ? _summand1 : _summand2);
            const BlastedPoly& termSummand     = (_summand1.isConstant() ? _summand2 : _summand1);
            const BVAnnotation& termType        = termSummand.term().type();

            return BlastedPoly(AnnotatedBVTerm(termType.withOffset(termType.offset() + constantSummand.constant()), termSummand.term().term()));
        } else {
            BVAnnotation annotation = BVAnnotation::forSum(_summand1.term().type(), _summand2.term().type());

            carl::BVTerm bvSummand1 = resizeBVTerm(_summand1.term(), annotation.width());
            carl::BVTerm bvSummand2 = resizeBVTerm(_summand2.term(), annotation.width());
            carl::BVTerm bvSum(carl::BVTermType::ADD, bvSummand1, bvSummand2);

            if(Settings::allow_encoding_into_complex_bvterms) {
                return BlastedPoly(AnnotatedBVTerm(annotation, bvSum), FormulasT());
            } else {
                AnnotatedBVTerm sum(annotation);
                FormulasT constraints;
                constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ, bvSum, sum.term())));
                return BlastedPoly(sum, constraints);
            }
        }
    }

    template<class Settings>
    BlastedPoly IntBlastModule<Settings>::blastProduct(const BlastedPoly& _factor1, const BlastedPoly& _factor2)
    {
        if(_factor1.isConstant() && _factor2.isConstant()) {
            return BlastedPoly(_factor1.constant() * _factor2.constant());
        } else if(_factor1.isConstant() || _factor2.isConstant()) {
            const BlastedPoly& constantFactor = (_factor1.isConstant() ? _factor1 : _factor2);
            const BlastedPoly& variableFactor = (_factor1.isConstant() ? _factor2 : _factor1);
            const BVAnnotation& variableType   = variableFactor.term().type();

            bool constantNegative = constantFactor.constant() < 0;
            BVAnnotation constantType(chooseWidth(constantFactor.constant(), 0, constantNegative), constantNegative, 0);
            BVAnnotation annotation = BVAnnotation::forProduct(variableType.withOffset(0), constantType).withOffset(variableType.offset() * constantFactor.constant());

            carl::BVTerm bvConstantFactor = encodeBVConstant(constantFactor.constant(), annotation);
            carl::BVTerm bvVariableFactor = resizeBVTerm(variableFactor.term(), annotation.width());
            carl::BVTerm bvProduct(carl::BVTermType::MUL, bvConstantFactor, bvVariableFactor);

            if(Settings::allow_encoding_into_complex_bvterms) {
                return BlastedPoly(AnnotatedBVTerm(annotation, bvProduct), FormulasT());
            } else {
                AnnotatedBVTerm product(annotation);
                FormulasT constraints;
                constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ, bvProduct, product.term())));
                return BlastedPoly(product, constraints);
            }
        } else {
            BVAnnotation annotation = BVAnnotation::forProduct(_factor1.term().type(), _factor2.term().type());

            carl::BVTerm bvFactor1 = resizeBVTerm(_factor1.term(), annotation.width());
            carl::BVTerm bvFactor2 = resizeBVTerm(_factor2.term(), annotation.width());
            carl::BVTerm bvProduct(carl::BVTermType::MUL, bvFactor1, bvFactor2);

            if(Settings::allow_encoding_into_complex_bvterms) {
                return BlastedPoly(AnnotatedBVTerm(annotation, bvProduct), FormulasT());
            } else {
                AnnotatedBVTerm product(annotation);
                FormulasT constraints;
                constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ, bvProduct, product.term())));
                return BlastedPoly(product, constraints);
            }
        }
    }

    template<class Settings>
    const BlastedConstr& IntBlastModule<Settings>::blastConstrTree(const ConstrTree& _constraint, FormulasT& _collectedFormulas)
    {
        const BlastedPoly& left = blastPolyTree(_constraint.left(), _collectedFormulas);
        const BlastedPoly& right = blastPolyTree(_constraint.right(), _collectedFormulas);

        auto blastedConstrIt = mConstrBlastings.find(_constraint.constraint());

        if(blastedConstrIt != mConstrBlastings.end()) {
            // This tree has already been encoded. Add its formulas to _collectedFormulas
            // and return the previously blasted node.
            const FormulasT& constraints = blastedConstrIt->second.constraints();
            _collectedFormulas.insert(_collectedFormulas.end(), constraints.begin(), constraints.end());
            return blastedConstrIt->second;
        }

        BlastedConstr blasted;
        bool simpleBlast = false;

        if(left.isConstant() && right.isConstant()) {
            blasted = BlastedConstr(evaluateRelation(_constraint.relation(), left.constant(), right.constant()));
            simpleBlast = true;
        } else {
            assert(left.isConstant() || right.isConstant()); // Our ConstrTree is constructed like that

            const BlastedPoly& constantPol = left.isConstant() ? left : right;
            const BlastedPoly& variablePol = left.isConstant() ? right : left;
            const Integer& constant = constantPol.constant();

            // Assuming "variable op constant" now (i.e., constant is on the right side)
            carl::Relation relation = left.isConstant() ? carl::turn_around(_constraint.relation()) : _constraint.relation();

            if(relation == carl::Relation::EQ || relation == carl::Relation::NEQ) {
                // is the constant outside the range of the variable?
                if(constant < variablePol.lowerBound() || constant > variablePol.upperBound()) {
                    blasted = BlastedConstr(_constraint.relation() == carl::Relation::NEQ);
                    simpleBlast = true;
                }
            } else { // relation is one of LESS, GREATER, LEQ, GEQ
                bool lowerEvaluation = evaluateRelation(_constraint.relation(), left.lowerBound(), constant);
                bool upperEvaluation = evaluateRelation(_constraint.relation(), left.upperBound(), constant);

                if(lowerEvaluation == upperEvaluation) {
                    blasted = BlastedConstr(lowerEvaluation);
                    simpleBlast = true;
                }
            }

            if(! simpleBlast) {
                // The constraint cannot be decided from the range of variablePol alone.
                // Translate into BV logic

                carl::BVTerm bvConstant = encodeBVConstant(constantPol.constant(), variablePol.term().type());

                carl::BVCompareRelation rel;

                switch(relation) {
                    case carl::Relation::EQ:
                        rel = carl::BVCompareRelation::EQ;
                        break;
                    case carl::Relation::NEQ:
                        rel = carl::BVCompareRelation::NEQ;
                        break;
                    case carl::Relation::LESS:
                        rel = (variablePol.term().type().isSigned() ? carl::BVCompareRelation::SLT : carl::BVCompareRelation::ULT);
                        break;
                    case carl::Relation::GREATER:
                        rel = (variablePol.term().type().isSigned() ? carl::BVCompareRelation::SGT : carl::BVCompareRelation::UGT);
                        break;
                    case carl::Relation::LEQ:
                        rel = (variablePol.term().type().isSigned() ? carl::BVCompareRelation::SLE : carl::BVCompareRelation::ULE);
                        break;
                    case carl::Relation::GEQ:
                        rel = (variablePol.term().type().isSigned() ? carl::BVCompareRelation::SGE : carl::BVCompareRelation::UGE);
                        break;
                    default:
                        assert(false);
                }

                blasted = BlastedConstr(FormulaT(carl::BVConstraint::create(rel, left.term().term(), bvConstant)));
            }
        }

        _collectedFormulas.insert(_collectedFormulas.end(), blasted.constraints().begin(), blasted.constraints().end());
        return mConstrBlastings.insert(std::make_pair(_constraint.constraint(), blasted)).first->second;
    }

    template<class Settings>
    bool IntBlastModule<Settings>::evaluateRelation(carl::Relation _relation, const Integer& _first, const Integer& _second) const
    {
        switch(_relation) {
            case carl::Relation::EQ:      return _first == _second;
            case carl::Relation::NEQ:     return _first != _second;
            case carl::Relation::LESS:    return _first <  _second;
            case carl::Relation::GREATER: return _first >  _second;
            case carl::Relation::LEQ:     return _first <= _second;
            case carl::Relation::GEQ:     return _first >= _second;
        }
        assert(false);
    }

    template<class Settings>
    const BlastedPoly& IntBlastModule<Settings>::blastPolyTree(const PolyTree& _poly, FormulasT& _collectedFormulas)
    {
        const BlastedPoly* left = nullptr;
        const BlastedPoly* right = nullptr;

        if(_poly.type() == PolyTree::Type::SUM || _poly.type() == PolyTree::Type::PRODUCT) {
            left = &(blastPolyTree(_poly.left(), _collectedFormulas));
            right = &(blastPolyTree(_poly.right(), _collectedFormulas));
        }

        auto blastedPolyIt = mPolyBlastings.find(_poly.poly());

        if(blastedPolyIt != mPolyBlastings.end()) {
            // This tree has already been encoded. Add its formulas to _collectedFormulas
            // and return the previously blasted node.
            const FormulasT& constraints = blastedPolyIt->second.constraints();
            _collectedFormulas.insert(_collectedFormulas.end(), constraints.begin(), constraints.end());
            return blastedPolyIt->second;
        }

        // Tree has not yet been encoded (only its subtrees, if any).

        BlastedPoly blasted;

        switch(_poly.type()) {
            case PolyTree::Type::CONSTANT: {
                blasted = BlastedPoly(_poly.constant());
                break;
            }
            case PolyTree::Type::VARIABLE: {
                // This should not happen.
                // Variables should have been blasted by 'blastVariable' method upfront.
                assert(false);
                break;
            }
            case PolyTree::Type::SUM:
            case PolyTree::Type::PRODUCT: {
                BlastedPoly intermediate = (_poly.type() == PolyTree::Type::SUM) ?
                                            blastSum(*left, *right) :
                                            blastProduct(*left, *right);

                if(Settings::apply_icp) {
                    // Obtain range from ICP substitute
                    carl::Variable substitute = mSubstitutes.at(_poly.poly());
                    IntegerInterval interval = getNum(mBoundsInRestriction.getInterval(substitute));
                    if(interval.lowerBoundType() == carl::BoundType::WEAK && interval.upperBoundType() == carl::BoundType::WEAK) {
                        auto shrunk = shrinkToRange(intermediate, interval);
                        blasted = shrunk.first;
                        if(shrunk.second) {
                            mShrunkPolys.insert(_poly.poly());
                        }
                    } else {
                        INTBLAST_DEBUG("Bad ICP interval for " << _poly.poly() << ": " << interval);
                        // assert(false);
                        blasted = intermediate;
                    }
                } else {
                    blasted = intermediate;
                }

                break;
            }
            default: {
                assert(false);
            }
        }

        _collectedFormulas.insert(_collectedFormulas.end(), blasted.constraints().begin(), blasted.constraints().end());
        return mPolyBlastings.insert(std::make_pair(_poly.poly(), blasted)).first->second;
    }

    template<class Settings>
    std::pair<BlastedPoly, bool> IntBlastModule<Settings>::shrinkToRange(const BlastedPoly& _input, const IntegerInterval& _interval) const
    {
        if(_interval.lowerBoundType() != carl::BoundType::WEAK || _interval.upperBoundType() != carl::BoundType::WEAK) {
            assert(false);
        }

        assert(_input.lowerBound() <= _interval.lower() && _input.upperBound() >= _interval.upper());

        if(_interval.isPointInterval()) {
            if(_input.isConstant()) {
                return std::make_pair(_input, false);
            } else {
                FormulasT constraints(_input.constraints());
                carl::BVTerm bvConstant = encodeBVConstant(_interval.lower(), _input.term().type());
                constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ, _input.term().term(), bvConstant)));
                return std::make_pair(BlastedPoly(_interval.lower(), constraints), true);
            }
        }

        // Interval is not a point interval, and interval is included in _input interval.
        // This also implies that _input is not constant.
        // Let's see whether resizing actually has any benefits.

        const BVAnnotation& inputType = _input.term().type();

        std::size_t newWidth = std::max(
            chooseWidth(_interval.lower() - inputType.offset(), 0, inputType.isSigned()),
            chooseWidth(_interval.upper() - inputType.offset(), 0, inputType.isSigned())
        );

        assert(newWidth <= inputType.width());
        if(newWidth == inputType.width()) {
            // Resizing is not possible, return _input without modifications
            return std::make_pair(_input, false);
        }

        // Resize to a new, smaller BlastedPoly
        FormulasT constraints(_input.constraints());
        AnnotatedBVTerm newTerm(inputType.withWidth(newWidth));

        constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                  carl::BVTerm(carl::BVTermType::EXTRACT, _input.term().term(), newWidth-1, 0),
                                                                  newTerm.term())));

        // add constraint which ensures a safe resizing
        carl::BVTermType extend = inputType.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U;
        constraints.push_back(FormulaT(carl::BVConstraint::create(
            carl::BVCompareRelation::EQ,
            carl::BVTerm(extend, newTerm.term(), inputType.width() - newWidth),
            _input.term().term()
        )));

        return std::make_pair(BlastedPoly(newTerm, constraints), true);
    }

    template<class Settings>
    FormulasT IntBlastModule<Settings>::blastConstraint(const ConstraintT& _constraint)
    {
        ConstrTree constraintTree(_constraint);
        FormulasT blastedFormulas;

        blastConstrTree(constraintTree, blastedFormulas);
        return blastedFormulas;
    }

    template<class Settings>
    Answer IntBlastModule<Settings>::checkCore()
    {
        mSolutionOrigin = SolutionOrigin::NONE;

        // Choose blastings for new variables,
        // and ensure compatibility of previous blastings for all variables

        bool reachedMaxWidth = false;
        for(auto variableWO : mInputVariables)
        {
            const carl::Variable& variable = variableWO.element();
            bool linear = ! mNonlinearInputVariables.contains(variable);
            IntegerInterval interval = getNum(mBoundsFromInput.getInterval(variable));

            Poly variablePoly(variable);
            auto blastingIt = mPolyBlastings.find(variablePoly);
            bool needsBlasting = (blastingIt == mPolyBlastings.end() || reblastingNeeded(blastingIt->second, interval, linear));

            if(needsBlasting)
            {
                if(blastingIt != mPolyBlastings.end()) {
                    unblastVariable(variable);
                }
                switch( blastVariable(variable, interval, linear) )
                {
                    case -1:
                        return callBackends();
                    case 0:
                        reachedMaxWidth = true;
                        break;
                    default:
                        break;
                }
            }
        }

        if(INTBLAST_DEBUG_ENABLED) {
            INTBLAST_DEBUG("Blastings:");
            for(auto blaPa : mPolyBlastings) {
                INTBLAST_DEBUG(blaPa.first << " --> " << blaPa.second);
            }

            INTBLAST_DEBUG("Substitutes:");
            for(auto substi : mSubstitutes) {
                INTBLAST_DEBUG(substi.first << " --> " << substi.second);
            }
        }

        Answer icpAnswer = UNKNOWN;

        if(Settings::apply_icp) {
            // Run ICP
            if(INTBLAST_DEBUG_ENABLED) {
                INTBLAST_DEBUG("Running ICP on these formulas:");

                for(const auto& formulaWO : *mpICPInput) {
                    INTBLAST_DEBUG(" - " << formulaWO.formula());
                    for(const auto& origin : formulaWO.origins()) {
                        INTBLAST_DEBUG("    (o) " << origin);
                    }
                }
            }
            icpAnswer = mICP.check();
            INTBLAST_DEBUG("icpAnswer: " << icpAnswer);

            if(icpAnswer == SAT && rReceivedFormula().satisfiedBy( mICP.model() ) == 1) {
                mSolutionOrigin = SolutionOrigin::ICP;
                return SAT;
            }
        }

        if(icpAnswer != UNSAT) {
            if(Settings::apply_icp) {
                INTBLAST_DEBUG("Updating bounds from ICP.");

                updateBoundsFromICP();
            }

            while(! mFormulasToEncode.empty()) {
                auto firstFormulaToEncode = mFormulasToEncode.begin();
                const FormulaT& formulaToEncode = *firstFormulaToEncode;
                encodeFormulaToBV(formulaToEncode);
                mFormulasToEncode.erase(firstFormulaToEncode);
            }

            INTBLAST_DEBUG("Running BV solver.");

            Answer bvAnswer = mpBVSolver->check();
            INTBLAST_DEBUG("Answer from BV solver: " << bvAnswer);

            if(bvAnswer == SAT) {
                 mSolutionOrigin = SolutionOrigin::BV;
                 return SAT;
            }
        }

        // At this point, the restriction is unsatisfiable
        // (determined either by the ICP module or by the BV solver).
        // Call backend

        if( reachedMaxWidth )
        {
            //updateOutsideRestrictionConstraint(icpAnswer == UNSAT);
            return callBackends();
        }
        if( rReceivedFormula().containsRealVariables() )
            return UNKNOWN;
        bool originalBoundsCovered = true;
        for(auto variableWO : mInputVariables)
        {
            const carl::Variable& variable = variableWO.element();
            IntegerInterval interval = getNum(mBoundsFromInput.getInterval(variable));

            Poly variablePoly(variable);
            auto blastingIt = mPolyBlastings.find( Poly(variable) );
            assert( blastingIt != mPolyBlastings.end() );
            const carl::Interval<Integer>& blastBounds = blastingIt->second.term().type().bounds();
            if( blastBounds != interval && !blastBounds.contains( interval ) )
            {
                originalBoundsCovered = false;
                break;
            }
        }
        if( originalBoundsCovered )
        {
            generateTrivialInfeasibleSubset();
            return UNSAT;
        }
        return UNKNOWN;
    }

    template<class Settings>
    Answer IntBlastModule<Settings>::callBackends()
    {
        INTBLAST_DEBUG("Running backend.");
        Answer backendAnswer = runBackends();
        INTBLAST_DEBUG("Answer from backend: " << backendAnswer);
        mSolutionOrigin = SolutionOrigin::BACKEND;

        if(backendAnswer == UNSAT) {
            getInfeasibleSubsets();
        }

        return backendAnswer;
    }

    template<class Settings>
    void IntBlastModule<Settings>::encodeFormulaToBV(const FormulaT& _formula)
    {
        INTBLAST_DEBUG("Formula " << _formula << " encoded to BV:");

        FormulasT bitvectorConstraints;
        carl::FormulaVisitor<FormulaT> visitor;
        std::function<FormulaT(FormulaT)> encodeConstraints = std::bind(&IntBlastModule::encodeConstraintToBV, this, std::placeholders::_1, &bitvectorConstraints);
        FormulaT bitvectorFormula = visitor.visitResult(_formula, encodeConstraints);

        addFormulaToBV(bitvectorFormula, _formula);

        for(const FormulaT& bitvectorConstraint : bitvectorConstraints) {
            addFormulaToBV(bitvectorConstraint, _formula);
        }
    }

    template<class Settings>
    FormulaT IntBlastModule<Settings>::encodeConstraintToBV(const FormulaT& _original, FormulasT* _collectedBitvectorConstraints)
    {
        if(_original.getType() == carl::FormulaType::CONSTRAINT && _original.constraint().integerValued())
        {
            ConstrTree constraintTree(_original.constraint());
            const BlastedConstr& blastedConstraint = blastConstrTree(constraintTree, *_collectedBitvectorConstraints);
            return blastedConstraint.formula();
        }
        return _original;
    }

    template<class Settings>
    bool IntBlastModule<Settings>::reblastingNeeded(const BlastedPoly& _previousBlasting, const IntegerInterval& _interval, bool _linear) const
    {
        if(_previousBlasting.isConstant()) {
            return ! _interval.isPointInterval() || _interval.lower() != _previousBlasting.constant();
        }

        const BVAnnotation& previousType = _previousBlasting.term().type();

        if(previousType.hasOffset() && ! _linear) {
            return true;
        }
        return previousType.bounds() != _interval && !previousType.bounds().contains(_interval);
    }

    template<class Settings>
    void IntBlastModule<Settings>::unblastVariable(const carl::Variable& _variable)
    {
        if(Settings::apply_icp) {
            removeBoundRestrictionsFromICP(_variable);
        }
        unblastPoly(Poly(_variable));
    }

    template<class Settings>
    int IntBlastModule<Settings>::blastVariable( const carl::Variable& _variable, const IntegerInterval& _interval, bool _allowOffset )
    {
        Poly variablePoly( _variable );
        if( _interval.isPointInterval() )
        {
            mPolyBlastings[variablePoly] = BlastedPoly( _interval.lower() );
        }

        std::size_t maxWidth = Settings::max_variable_encoding_width;
        _allowOffset = _allowOffset && Settings::use_offsets_in_encoding;

        /* 
         * If interval is unbounded:
         *   Start with no offset, signed, maximum width (tempType)
         *     If offset is not allowed
         *       Remove sign if interval is semi-positive
         *     Else:
         *       If lower bound of interval is higher than tempType's lower bound, shift range using offset and remove sign
         *       (similar for upper bound)
         *
         *  If interval is bounded:
         *   If offset allowed:
         *     Lower bound as offset, width "as small as possible" (at most maximum width), unsigned
         *   Else:
         *     Make signed iff interval not semipositive
         *     Width "as small as possible" (at most maximum width)
         */

        BVAnnotation blastedType;
        int ret = 1;
        if( _interval.lowerBoundType() == carl::BoundType::INFTY || _interval.upperBoundType() == carl::BoundType::INFTY )
        {
            if( _allowOffset )
            {
                BVAnnotation tempType( maxWidth, true, 0 );
                
                if( _interval.lowerBoundType() != carl::BoundType::INFTY && _interval.lower() > tempType.lowerBound() )
                {
                    blastedType = BVAnnotation( maxWidth, false, _interval.lower() );
                }
                else if( _interval.upperBoundType() != carl::BoundType::INFTY && _interval.upper() < tempType.upperBound() )
                {
                    blastedType = BVAnnotation( maxWidth, false, _interval.upper() - (tempType.upperBound() - tempType.lowerBound()) );
                }
                else
                {
                    blastedType = tempType;
                }
            } 
            else
            {
                if( maxWidth == 0 )
                    return -1;
                blastedType = BVAnnotation( maxWidth, !_interval.isSemiPositive(), 0 );
            }
            ret = 0;
        }
        else
        {
            // interval is bounded
            std::size_t width = 0;
            if( _allowOffset )
            {
                width = chooseWidth( _interval.upper() - _interval.lower(), maxWidth, false );
                blastedType = BVAnnotation( width, false, _interval.lower() );
            }
            else
            {
                if( _interval.isSemiPositive() )
                {
                    width = chooseWidth( _interval.upper(), maxWidth, false );
                    blastedType = BVAnnotation( width, false, 0 );
                }
                else // @todo: do something clever, if semi-negative
                {
                    std::size_t widthForUpper = chooseWidth( _interval.upper(), maxWidth, true );
                    std::size_t widthForLower = chooseWidth(_interval.lower(), maxWidth, true );
                    width = std::max( widthForUpper, widthForLower );
                    blastedType = BVAnnotation( width, true, 0 );
                }
            }
            if( maxWidth > 0 )
                ret = width <= maxWidth ? 1 : 0;
        }

        if( Settings::apply_icp )
        {
            addBoundRestrictionsToICP( _variable, blastedType );
        }

        mPolyBlastings[variablePoly] = BlastedPoly( AnnotatedBVTerm(blastedType) );
        return ret;
    }

    template<class Settings>
    void IntBlastModule<Settings>::addBoundRestrictionsToICP(carl::Variable _variable, const BVAnnotation& blastedType)
    {
        addFormulaToICP(FormulaT(ConstraintT(_variable, carl::Relation::GEQ, blastedType.lowerBound())), mConstraintFromBounds);
        addFormulaToICP(FormulaT(ConstraintT(_variable, carl::Relation::LEQ, blastedType.upperBound())), mConstraintFromBounds);
    }

    template<class Settings>
    void IntBlastModule<Settings>::removeBoundRestrictionsFromICP(carl::Variable _variable)
    {
        auto& blastedVariable = mPolyBlastings.at(Poly(_variable));

        if(! blastedVariable.isConstant()) {
            const BVAnnotation& blastedType = blastedVariable.term().type();

            removeFormulaFromICP(FormulaT(ConstraintT(_variable, carl::Relation::GEQ, blastedType.lowerBound())), mConstraintFromBounds);
            removeFormulaFromICP(FormulaT(ConstraintT(_variable, carl::Relation::LEQ, blastedType.upperBound())), mConstraintFromBounds);
        }
    }

    template<class Settings>
    std::size_t IntBlastModule<Settings>::chooseWidth(const Integer& _numberToCover, std::size_t _maxWidth, bool _signed) const
    {
        assert(_numberToCover >= 0 || _signed);
        std::size_t width = 1;
        carl::Interval<Integer> interval(Integer(_signed ? -1 : 0), Integer(_signed ? 0 : 1));
        while((width < _maxWidth || _maxWidth == 0) && !interval.contains(_numberToCover)) {
            ++width;
            interval.setLower(interval.lower() * 2);
            interval.setUpper((interval.upper()+1)*2 - 1);
        }
        return width;
    }

    template<class Settings>
    void IntBlastModule<Settings>::updateBoundsFromICP()
    {
        for(const FormulaT formula : mProcessedFormulasFromICP) {
            mBoundsInRestriction.removeBound(formula.constraint(), formula);
        }
        mProcessedFormulasFromICP.clear();

        for(ModuleInput::const_iterator fwo=mICP.rPassedFormula().begin(); fwo != mICP.rPassedFormula().end(); fwo++) {
           if(INTBLAST_DEBUG_ENABLED) INTBLAST_DEBUG("from ICP: " << fwo->formula());
           mBoundsInRestriction.addBound(fwo->formula().constraint(), fwo->formula());
           mProcessedFormulasFromICP.push_back(fwo->formula());
        }
        
        FormulasT icpBounds = mICP.getCurrentBoxAsFormulas();
        for( auto& f : icpBounds ) {
            if(INTBLAST_DEBUG_ENABLED) INTBLAST_DEBUG("from ICP: " << f);
            mBoundsInRestriction.addBound(f.constraint(), f);
            mProcessedFormulasFromICP.push_back(f);
        }
        recheckShrunkPolys();
    }

    template<class Settings>
    void IntBlastModule<Settings>::updateOutsideRestrictionConstraint(bool _fromICPOnly)
    {
        FormulasT outsideConstraints;

        auto& inputBounds = mBoundsFromInput.getEvalIntervalMap();
        for(auto& variableWithOrigins : mInputVariables) {
            const carl::Variable& variable = variableWithOrigins.element();
            auto& blastedVar = mPolyBlastings.at(Poly(variable));
            Integer blastedLowerBound = (blastedVar.isConstant() ? blastedVar.constant() : blastedVar.term().type().lowerBound());
            Integer blastedUpperBound = (blastedVar.isConstant() ? blastedVar.constant() : blastedVar.term().type().upperBound());
            auto inputBoundsIt = inputBounds.find(variable);

            if(inputBoundsIt == inputBounds.end() || getNum(inputBoundsIt->second).contains(blastedLowerBound - 1)) {
                outsideConstraints.push_back(FormulaT(ConstraintT(variable, carl::Relation::LESS, blastedLowerBound)));
            }

            if(inputBoundsIt == inputBounds.end() || getNum(inputBoundsIt->second).contains(blastedUpperBound + 1)) {
                outsideConstraints.push_back(FormulaT(ConstraintT(variable, carl::Relation::GREATER, blastedUpperBound)));
            }
        }

        FormulaT newOutsideConstraint(carl::FormulaType::OR, outsideConstraints);

        // Construct origins of the "outside restriction" constraint.
        // They should be picked in a suitable way for the infeasible subset derivation.

        // If the ICP module has returned UNSAT, we can use the infeasible subset from ICP.
        // The origins of the constraints are turned into a conjunction and inserted as
        // one origin of the "outside restriction" constraint.

        // If the ICP module has returned UNKNOWN, and the BV module has returned UNSAT,
        // the infeasible subset of the BV module is not sufficient: When encoding into
        // Bitvector logic, the contracted bounds from ICP are used and become an implicit
        // constraint of the Bitvector problem. However, the ICP module currently does not
        // give us any insights about the constraints which have been used to contract
        // a certain clause. Therefore, we cannot create a reasonable infeasible subset here.
        // Instead, we use the conjunction of all input formulas as origin of the
        // "outside restriction" constraint.

        FormulaSetT origins;

        if(_fromICPOnly) {
            const std::vector<FormulaSetT>& infeasibleInRestriction = mICP.infeasibleSubsets();
            ModuleInput* restrictionInput = mpICPInput;

            for(const FormulaSetT& infeasibleSubset : infeasibleInRestriction) {
                FormulasT originsOfInfSubset;
                for(const FormulaT& infSubsetElement : infeasibleSubset) {
                    // Collect origins of element (i.e. subformulas of the received formula of IntBlastModule)
                    ModuleInput::const_iterator posInModuleInput = restrictionInput->find(infSubsetElement);
                    assert(posInModuleInput != restrictionInput->end());
                    if(posInModuleInput->hasOrigins()) {
                        bool isConstraintFromRestriction = false;
                        for(const auto& origin : posInModuleInput->origins()) {
                            if(origin == mConstraintFromBounds) {
                                isConstraintFromRestriction = true;
                                break;
                            }
                        }

                        if(! isConstraintFromRestriction) {
                            collectOrigins(*findBestOrigin(posInModuleInput->origins()), originsOfInfSubset);
                        }
                    }
                }
                origins.insert(FormulaT(carl::FormulaType::AND, originsOfInfSubset));
            }
        } else {
            FormulasT allInputFormulas;
            for(const auto& inputFormula : rReceivedFormula()) {
                allInputFormulas.push_back(inputFormula.formula());
            }
            origins.insert(FormulaT(carl::FormulaType::AND, allInputFormulas));
        }

        if(INTBLAST_DEBUG_ENABLED) {
            INTBLAST_DEBUG("'outside restriction' formula has origins:");
            for(const FormulaT& origin : origins) {
                INTBLAST_DEBUG("- " << origin);
            }
        }

        addSubformulaToPassedFormula(newOutsideConstraint, std::make_shared<std::vector<FormulaT>>(origins.begin(), origins.end()));
    }

    template<class Settings>
    void IntBlastModule<Settings>::addFormulaToICP(const FormulaT& _formula, const FormulaT& _origin)
    {
        INTBLAST_DEBUG("-[ICP+]-> " << _formula);
        INTBLAST_DEBUG("          (origin: " << _origin << ")");
        auto insertionResult = mpICPInput->add(_formula, _origin);

        if(insertionResult.second) {
            mICP.inform(_formula);
            mICP.add(insertionResult.first);
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::addSubstitutesToICP(const ConstraintT& _constraint, const FormulaT& _origin)
    {
        // Create a substitute for every node of the constraint tree of _formula
        // in order to receive bounds from ICP for these expressions

        ConstrTree constraintTree(_constraint);

        // Walk through the ConstraintTree in a breadth-first search
        std::list<PolyTree> nodesForSubstitution;
        nodesForSubstitution.push_back(constraintTree.left());
        nodesForSubstitution.push_back(constraintTree.right());

        while(! nodesForSubstitution.empty()) {
            const PolyTree& currentPoly = nodesForSubstitution.front();

            Poly substituteEq;

            switch(currentPoly.type()) {
                case PolyTree::Type::SUM:
                    substituteEq = Poly(getICPSubstitute(currentPoly.left().poly()))
                                      + getICPSubstitute(currentPoly.right().poly());
                    break;
                case PolyTree::Type::PRODUCT:
                    substituteEq = Poly(getICPSubstitute(currentPoly.left().poly()))
                                      * getICPSubstitute(currentPoly.right().poly());
                    break;
                default:
                    substituteEq = currentPoly.poly();
            }

            substituteEq -= getICPSubstitute(currentPoly.poly());
            FormulaT constraintForICP(substituteEq, carl::Relation::EQ);
            addFormulaToICP(constraintForICP, _origin);

            if(currentPoly.type() == PolyTree::Type::SUM || currentPoly.type() == PolyTree::Type::PRODUCT) {
                // Schedule left and right subtree of current PolyTree
                // for being visited in the breadth-first search
                nodesForSubstitution.push_back(currentPoly.left());
                nodesForSubstitution.push_back(currentPoly.right());
            }

            nodesForSubstitution.pop_front();
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::addConstraintFormulaToICP(const FormulaT& _formula)
    {
        assert(_formula.getType() == carl::FormulaType::CONSTRAINT);
        ConstrTree constraintTree(_formula.constraint());

        // Add the root (the constraint itself) to ICP
        Poly rootPoly(getICPSubstitute(constraintTree.left().poly()));
        rootPoly -= getICPSubstitute(constraintTree.right().poly());
        ConstraintT rootConstraint(rootPoly, constraintTree.relation());

        addFormulaToICP(FormulaT(rootConstraint), _formula);
    }

    template<class Settings>
    carl::Variable::Arg IntBlastModule<Settings>::getICPSubstitute(const Poly& _poly)
    {
        auto substituteLookup = mSubstitutes.find(_poly);
        if(substituteLookup != mSubstitutes.end()) {
            return substituteLookup->second;
        }

        mSubstitutes[_poly] = carl::freshIntegerVariable();
        return mSubstitutes[_poly];
    }

    template<class Settings>
    void IntBlastModule<Settings>::removeFormulaFromICP(const FormulaT& _formula, const FormulaT& _origin)
    {
        auto formulaInInput = mpICPInput->find(_formula);
        if(formulaInInput != mpICPInput->end()) {
            if(mpICPInput->removeOrigin(formulaInInput, _origin)) {
                INTBLAST_DEBUG("-[ICP-]-> " << _formula);
                mICP.remove(formulaInInput);
                mpICPInput->erase(formulaInInput);
            }
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::removeOriginFromICP(const FormulaT& _origin)
    {
        ModuleInput::iterator icpFormula = mpICPInput->begin();
        while(icpFormula != mpICPInput->end())
        {
            // Remove the given formula from the set of origins.
            if(mpICPInput->removeOrigin(icpFormula, _origin)) {
                INTBLAST_DEBUG("-[ICP-]-> " << icpFormula->formula());
                mICP.remove(icpFormula);
                icpFormula = mpICPInput->erase(icpFormula);
            } else {
                ++icpFormula;
            }
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::addFormulaToBV(const FormulaT& _formula, const FormulaT& _origin)
    {
        INTBLAST_DEBUG("-[BV +]-> " << _formula);
        INTBLAST_DEBUG("          (origin: " << _origin << ")");

        auto insertionResult = mpBVInput->add(_formula, _origin);
        if(insertionResult.second) { // The formula was fresh
            mpBVSolver->inform(_formula);
            mpBVSolver->add(_formula);
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::removeOriginFromBV(const FormulaT& _origin)
    {
        ModuleInput::iterator bvFormula = mpBVInput->begin();
        while(bvFormula != mpBVInput->end())
        {
            // Remove the given formula from the set of origins.
            if(mpBVInput->removeOrigin(bvFormula, _origin)) {
                mpBVSolver->removeFormula(bvFormula->formula());
                bvFormula = mpBVInput->erase(bvFormula);
            } else {
                ++bvFormula;
            }
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::updateModelFromICP() const
    {
        clearModel();
        mICP.updateModel();
        mModel = mICP.model();
    }

    template<class Settings>
    void IntBlastModule<Settings>::updateModelFromBV() const
    {
        clearModel();
        const Model& bvModel = mpBVSolver->model();

        // Transfer all non-bitvector assignments
        for(const auto& varAndValue : bvModel) {
            if(! varAndValue.first.isBVVariable()) {
                mModel.insert(varAndValue);
            }
        }

        // For each input variable, look up bitvector value and convert it back to integer
        for(auto inputVariableIt = mInputVariables.cbegin();inputVariableIt != mInputVariables.cend();++inputVariableIt) {
            auto& inputVariable = *inputVariableIt;
            const carl::Variable& variable = inputVariable.element();
            const BlastedPoly& blasting = mPolyBlastings.at(Poly(variable));

            if(blasting.isConstant()) {
                auto modelValue = carl::RealAlgebraicNumber<Rational>(blasting.constant());
                mModel.emplace(ModelVariable(variable), ModelValue(modelValue));
            } else {
                const carl::BVTerm& blastedTerm = blasting.term().term();
                assert(blastedTerm.type() == carl::BVTermType::VARIABLE);
                const carl::BVVariable& bvVariable = blastedTerm.variable();

                Integer integerValue(0);

                auto bvValueInModel = bvModel.find(ModelVariable(bvVariable));
                if(bvValueInModel != bvModel.end()) {
                    const carl::BVValue& bvValue = bvValueInModel->second.asBVValue();
                    integerValue = decodeBVConstant(bvValue, blasting.term().type());
                }
                // If the bitvector variable does not appear in the model of the
                // BV solver, the BV solver has not received any constraints
                // containing this variable. This implies that an arbitrary value is allowed.
                // We simply use constant 0.
                mModel.emplace(ModelVariable(variable), ModelValue(integerValue));
            }
        }
    }

    template<class Settings>
    typename IntBlastModule<Settings>::IntegerInterval IntBlastModule<Settings>::getNum(const RationalInterval& _interval) const
    {
        return IntegerInterval(
            carl::getNum(_interval.lower()), _interval.lowerBoundType(),
            carl::getNum(_interval.upper()), _interval.upperBoundType()
        );
    }

    template<class Settings>
    void IntBlastModule<Settings>::addPolyParents(const ConstraintT& _constraint)
    {
        ConstrTree constraintTree(_constraint);

        // Perform a BFS
        std::list<PolyTree> nodes;
        nodes.push_back(constraintTree.left());
        nodes.push_back(constraintTree.right());

        while(! nodes.empty()) {
            const PolyTree& current = nodes.front();

            if(current.type() == PolyTree::Type::SUM || current.type() == PolyTree::Type::PRODUCT) {
                addPolyParent(current.left().poly(), current.poly());
                addPolyParent(current.right().poly(), current.poly());
                nodes.push_back(current.left());
                nodes.push_back(current.right());
            }

            nodes.pop_front();
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::addPolyParent(const Poly& _child, const Poly& _parent)
    {
        auto inserted = mPolyParents.insert(std::make_pair(_child, std::set<Poly>()));
        inserted.first->second.insert(_parent);
    }

    template<class Settings>
    std::set<Poly> IntBlastModule<Settings>::parentalClosure(std::set<Poly> _children)
    {
        std::set<Poly> closure(_children);
        std::list<Poly> incomplete(_children.begin(), _children.end());

        while(! incomplete.empty()) {
            const Poly& current = incomplete.front();
            for(auto parent : mPolyParents[current]) {
                auto parentInserted = closure.insert(parent);
                if(parentInserted.second) {
                    incomplete.push_back(parent);
                }
            }
            incomplete.pop_front();
        }

        return closure;
    }

    template<class Settings>
    void IntBlastModule<Settings>::recheckShrunkPolys()
    {
        auto& icpBounds = mBoundsInRestriction.getEvalIntervalMap();
        std::set<Poly> polysToReencode;

        for(const Poly& shrunkPoly : mShrunkPolys) {
            auto& blastedPoly = mPolyBlastings.at(shrunkPoly);
            auto& substitute = mSubstitutes.at(shrunkPoly);

            IntegerInterval encodedBounds = IntegerInterval(blastedPoly.lowerBound(), blastedPoly.upperBound());
            auto icpBoundsIt = icpBounds.find(substitute);

            if(icpBoundsIt == icpBounds.end() || ! encodedBounds.contains(getNum(icpBoundsIt->second))) {
                polysToReencode.insert(shrunkPoly);
            }
        }

        if(! polysToReencode.empty()) {
            unblastPolys(polysToReencode);
        }
    }

    template<class Settings>
    void IntBlastModule<Settings>::unblastPoly(const Poly& _polys)
    {
        std::set<Poly> polySet;
        polySet.insert(_polys);
        unblastPolys(polySet);
    }

    template<class Settings>
    void IntBlastModule<Settings>::unblastPolys(const std::set<Poly>& _polys)
    {
        std::set<Poly> obsolete = parentalClosure(_polys);

        // Erase all PolyBlastings belonging to the polynomials in 'obsolete'
        auto polyIt = mPolyBlastings.begin();
        while(polyIt != mPolyBlastings.end()) {
            if(obsolete.find(polyIt->first) != obsolete.end()) {
                mShrunkPolys.erase(polyIt->first);
                polyIt = mPolyBlastings.erase(polyIt);
            } else {
                ++polyIt;
            }
        }

        // Erase all ConstrBlastings which used a PolyBlasting that is now deleted
        auto constrIt = mConstrBlastings.begin();
        while(constrIt != mConstrBlastings.end()) {
            ConstrTree constrTree(constrIt->first);
            if(obsolete.find(constrTree.left().poly()) != obsolete.end()) {
                constrIt = mConstrBlastings.erase(constrIt);
            } else {
                ++constrIt;
            }
        }

        // Reencode all formulas which contain constraints whose
        // ConstrBlastings is now deleted
        for(const auto& inputFormula : rReceivedFormula()) {
            std::vector<ConstraintT> constraintsInFormula;
            inputFormula.formula().getConstraints(constraintsInFormula);

            bool needsReencoding = false;
            for(const ConstraintT& constraint : constraintsInFormula) {
                if(mConstrBlastings.find(constraint) == mConstrBlastings.end()) {
                    needsReencoding = true;
                    break;
                }
            }

            if(needsReencoding) {
                removeOriginFromBV(inputFormula.formula());
                mFormulasToEncode.insert(inputFormula.formula());
            }
        }
    }
}

#include "Instantiation.h"
