/**
 * @file IntBlastModule.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-05-12
 * Created on 2015-05-12.
 */

#include "IntBlastModule.h"
#include "../AddModules.h"

namespace smtrat
{
    /**
     * Constructors.
     */

    IntBlastModule::IntBlastModule( ModuleType _type, const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager ):
    Module( _type, _formula, _conditionals, _manager ),
    mBoundsFromInput(),
    mBoundsInRestriction(),
    mInputVariables(),
    mNonlinearInputVariables(),
    mpICPInput(new ModuleInput()),
    mICPFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
    mpICPRuntimeSettings(new RuntimeSettings()),
    mICP(MT_ICPModule, mpICPInput, mpICPRuntimeSettings, mICPFoundAnswer),
    mConstraintFromBounds(carl::freshBooleanVariable()),
    mProcessedFormulasFromICP(),
    mpBVInput(new ModuleInput()),
    mpBVSolver(new BVSolver()),
    mFormulasToEncode(),
    mOutsideRestriction(carl::FormulaType::TRUE),
    mOutsideRestrictionOrigin(carl::freshBooleanVariable()),
    mSolutionOrigin(SolutionOrigin::NONE),
    mPolyBlastings(),
    mConstrBlastings(),
    mSubstitutes(),
    mSubstitutedPolys()
    {
        smtrat::addModules(mpBVSolver);
        // TODO: Do we have to do some more initialization stuff here? Settings?

        std::cout << "IBM: initialization" << std::endl;
    }

    /**
     * Destructor.
     */

    IntBlastModule::~IntBlastModule()
    {
        delete mpICPInput;
        while( !mICPFoundAnswer.empty() )
        {
            std::atomic_bool* toDel = mICPFoundAnswer.back();
            mICPFoundAnswer.pop_back();
            delete toDel;
        }
        mICPFoundAnswer.clear();
        delete mpICPRuntimeSettings;

        delete mpBVSolver;
        delete mpBVInput;
    };

    bool IntBlastModule::informCore( const FormulaT& _constraint )
    {
        informBackends(_constraint);
        return true;
    }

    void IntBlastModule::init()
    {}

    bool IntBlastModule::addCore( ModuleInput::const_iterator _subformula )
    {
        const FormulaT& formula = _subformula->formula();
        assert(formula.getType() == carl::FormulaType::CONSTRAINT);
        assert(formula.constraint().integerValued());

        // Retrieve all integer-valued variables in formula
        carl::Variables variablesInFormula;
        carl::Variables nonlinearVariablesInFormula;
        const Poly& poly = formula.constraint().lhs();
        formula.integerValuedVars(variablesInFormula);
        for(auto termIt = poly.begin();termIt != poly.end();++termIt) {
            if(termIt->getNrVariables() > 1 || ! termIt->isLinear()) {
                termIt->gatherVariables(nonlinearVariablesInFormula);
            }
        }

        // Update 'mInputVariables' and 'mNonlinearInputVariables' sets
        for(auto& variable : variablesInFormula) {
            mInputVariables.add(variable, formula);
        }
        for(auto& variable : variablesInFormula) {
            mNonlinearInputVariables.add(variable, formula);
        }

        // Update mBoundsFromInput using the new formula
        mBoundsFromInput.addBound(formula.constraint(), formula);

        // Schedule formula for encoding to BV logic
        mFormulasToEncode.push_back(formula);

        // Pass new formula to ICP, generating substitutes
        addConstraintToICP(formula);

        return ! mBoundsFromInput.isConflicting();
    }

    void IntBlastModule::removeCore( ModuleInput::const_iterator _subformula )
    {
        const FormulaT& formula = _subformula->formula();

        mInputVariables.removeOrigin(formula);
        mNonlinearInputVariables.removeOrigin(formula);

        mBoundsFromInput.removeBound(formula.constraint(), formula);
        // mBoundsInRestriction: updated by updateBoundsFromICP() in next check

        removeOriginFromICP(formula);
        removeOriginFromBV(formula);

        mFormulasToEncode.remove(formula);
    }

    void IntBlastModule::updateModel() const
    {
        mModel.clear();
        if(solverState() == True)
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

    carl::BVTerm IntBlastModule::encodeBVConstant(const Integer& _constant, const BlastedType& _type) const
    {
        assert(_constant >= _type.lowerBound() && _constant <= _type.upperBound());
        carl::BVValue constValue(_type.width(), _constant - _type.offset());
        return carl::BVTerm(carl::BVTermType::CONSTANT, constValue);
    }

    Integer IntBlastModule::decodeBVConstant(const carl::BVValue& _value, const BlastedType& _type) const
    {
        Integer summand(1);
        Integer converted(0);

        // Unsigned conversion from binary to integer
        for(std::size_t position = 0;position<_value.width();++position) {
            if(_value[position]) {
                converted += summand;
            }
            summand *= 2;
        }

        // For negative numbers in two's complement, substract 2^width from result
        if(_type.isSigned() && _value[_value.width()-1]) {
            converted -= summand;
        }

        return converted + _type.offset();
    }

    carl::BVTerm IntBlastModule::resizeBVTerm(const BlastedTerm& _term, std::size_t _width) const
    {
        assert(_width >= _term.type().width());

        if(_width == _term.type().width()) {
            return _term.term();
        } else {
            carl::BVTermType ext = (_term.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U);
            return carl::BVTerm(ext, _term.term(), _width - _term.type().width());
        }
    }

    BlastedPoly IntBlastModule::blastSum(const BlastedPoly& _summand1, const BlastedPoly& _summand2)
    {
        if(_summand1.isConstant() && _summand2.isConstant()) {
            return BlastedPoly(_summand1.constant() + _summand2.constant());
        } else if(_summand1.isConstant() || _summand2.isConstant()) {
            const BlastedPoly& constantSummand = (_summand1.isConstant() ? _summand1 : _summand2);
            const BlastedPoly& termSummand     = (_summand1.isConstant() ? _summand2 : _summand1);
            const BlastedType& termType        = termSummand.term().type();

            return BlastedPoly(BlastedTerm(termType.withOffset(termType.offset() + constantSummand.constant()), termSummand.term().term()));
        } else {
            FormulasT constraints;
            BlastedTerm sum(BlastedType::forSum(_summand1.term().type(), _summand2.term().type()));

            carl::BVTerm bvSummand1 = resizeBVTerm(_summand1.term(), sum.type().width());
            carl::BVTerm bvSummand2 = resizeBVTerm(_summand2.term(), sum.type().width());

            constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                      carl::BVTerm(carl::BVTermType::ADD, bvSummand1, bvSummand2),
                                                                      sum.term())));
            return BlastedPoly(sum, constraints);
        }
    }

    BlastedPoly IntBlastModule::blastProduct(const BlastedPoly& _factor1, const BlastedPoly& _factor2)
    {
        if(_factor1.isConstant() && _factor2.isConstant()) {
            return BlastedPoly(_factor1.constant() * _factor2.constant());
        } else if(_factor1.isConstant() || _factor2.isConstant()) {
            const BlastedPoly& constantFactor = (_factor1.isConstant() ? _factor1 : _factor2);
            const BlastedPoly& variableFactor = (_factor1.isConstant() ? _factor2 : _factor1);
            const BlastedType& variableType   = variableFactor.term().type();

            bool constantNegative = constantFactor.constant() < 0;
            BlastedType constantType(chooseWidth(constantFactor.constant(), 0, constantNegative), constantNegative, 0);
            BlastedTerm product(BlastedType::forProduct(variableType.withOffset(0), constantType).withOffset(variableType.offset() * constantFactor.constant()));

            carl::BVTerm bvConstantFactor = encodeBVConstant(constantFactor.constant(), product.type());
            carl::BVTerm bvVariableFactor = resizeBVTerm(variableFactor.term(), product.type().width());

            FormulasT constraints;
            constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                      carl::BVTerm(carl::BVTermType::MUL, bvConstantFactor, bvVariableFactor),
                                                                      product.term())));
            return BlastedPoly(product, constraints);
        } else {
            FormulasT constraints;
            BlastedTerm product(BlastedType::forProduct(_factor1.term().type(), _factor2.term().type()));

            carl::BVTerm bvFactor1 = resizeBVTerm(_factor1.term(), product.type().width());
            carl::BVTerm bvFactor2 = resizeBVTerm(_factor2.term(), product.type().width());

            constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                      carl::BVTerm(carl::BVTermType::MUL, bvFactor1, bvFactor2),
                                                                      product.term())));
            return BlastedPoly(product, constraints);
        }
    }

    const BlastedConstr& IntBlastModule::blastConstrTree(const ConstrTree& _constraint, FormulasT& _collectedFormulas)
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
            carl::Relation relation = left.isConstant() ? carl::turnAroundRelation(_constraint.relation()) : _constraint.relation();

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

        if(! blasted.formula().isTrue()) {
            _collectedFormulas.push_back(blasted.formula());
        }
        _collectedFormulas.insert(_collectedFormulas.end(), blasted.constraints().begin(), blasted.constraints().end());
        return mConstrBlastings.insert(std::make_pair(_constraint.constraint(), blasted)).first->second;
    }

    bool IntBlastModule::evaluateRelation(carl::Relation _relation, const Integer& _first, const Integer& _second) const
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

    const BlastedPoly& IntBlastModule::blastPolyTree(const PolyTree& _poly, FormulasT& _collectedFormulas)
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

                // Obtain range from ICP substitute
                carl::Variable substitute = mSubstitutes.at(_poly.poly());
                IntegerInterval interval = getNum(mBoundsInRestriction.getInterval(substitute));
                assert(interval.lowerBoundType() == carl::BoundType::WEAK && interval.upperBoundType() == carl::BoundType::WEAK);

                blasted = reduceToRange(intermediate, interval);
                break;
            }
            default: {
                assert(false);
            }
        }

        _collectedFormulas.insert(_collectedFormulas.end(), blasted.constraints().begin(), blasted.constraints().end());
        return mPolyBlastings.insert(std::make_pair(_poly.poly(), blasted)).first->second;
    }

    BlastedPoly IntBlastModule::reduceToRange(const BlastedPoly& _input, const IntegerInterval& _interval) const
    {
        if(_interval.lowerBoundType() != carl::BoundType::WEAK || _interval.upperBoundType() != carl::BoundType::WEAK) {
            assert(false);
        }

        assert(_input.lowerBound() <= _interval.lower() && _input.upperBound() >= _interval.upper());

        if(_interval.isPointInterval()) {
            if(_input.isConstant()) {
                return _input;
            } else {
                FormulasT constraints(_input.constraints());
                carl::BVTerm bvConstant = encodeBVConstant(_interval.lower(), _input.term().type());
                constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ, _input.term().term(), bvConstant)));
                return BlastedPoly(_interval.lower(), constraints);
            }
        }

        // Interval is not a point interval, and interval is included in _input interval.
        // This also implies that _input is not constant.
        // Let's see whether resizing actually has any benefits.

        const BlastedType& inputType = _input.term().type();

        std::size_t newWidth = std::max(
            chooseWidth(_interval.lower() - inputType.offset(), 0, inputType.isSigned()),
            chooseWidth(_interval.upper() - inputType.offset(), 0, inputType.isSigned())
        );

        assert(newWidth <= inputType.width());
        if(newWidth == inputType.width()) {
            // Resizing is not possible, return _input without modifications
            return _input;
        }

        // Resize to a new, smaller BlastedPoly
        FormulasT constraints(_input.constraints());
        BlastedTerm newTerm(inputType.withWidth(newWidth));

        constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                  carl::BVTerm(carl::BVTermType::EXTRACT, _input.term().term(), newWidth-1, 0),
                                                                  newTerm.term())));

        // add constraints which ensure a safe resizing
        if(inputType.isSigned()) {
            // All removed bits must equal the msb of newTerm.term()
            constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                      carl::BVTerm(carl::BVTermType::EXTRACT, _input.term().term(), inputType.width()-1, newWidth),
                                                                      carl::BVTerm(carl::BVTermType::EXTRACT, _input.term().term(), inputType.width()-2, newWidth-1))));
        } else { // type is unsigned
            // All removed bits must be zero
            constraints.push_back(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                      carl::BVTerm(carl::BVTermType::EXTRACT, _input.term().term(), inputType.width()-1, newWidth),
                                                                      carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(inputType.width() - newWidth, 0)))));
        }

        return BlastedPoly(newTerm, constraints);
    }

    FormulasT IntBlastModule::blastConstraint(const ConstraintT& _constraint)
    {
        ConstrTree constraintTree(_constraint);
        FormulasT blastedFormulas;

        blastConstrTree(constraintTree, blastedFormulas);
        return blastedFormulas;
    }

    Answer IntBlastModule::checkCore(bool _full)
    {
        mSolutionOrigin = SolutionOrigin::NONE;

        // Choose blastings for new variables,
        // and ensure compatibility of previous blastings for all variables

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
                blastVariable(variable, interval, linear);
            }
        }

        std::cout << "Blastings:" << std::endl;
        for(auto blaPa : mPolyBlastings) {
            std::cout << blaPa.first << " --> " << blaPa.second << std::endl;
        }

        std::cout << "Substitutes:" << std::endl;
        for(auto substi : mSubstitutes) {
            std::cout << substi.first << " --> " << substi.second << std::endl;
        }

        // Run ICP
        Answer icpAnswer = mICP.check();
        std::cout << "icpAnswer: " << (icpAnswer == True ? "True" : (icpAnswer == False ? "False" : "Unknown")) << std::endl;

        if(icpAnswer == True) {
            mSolutionOrigin = SolutionOrigin::ICP;
            return True;
        }

        if(icpAnswer == Unknown) {
            std::cout << "Updating bounds from ICP." << std::endl;
            updateBoundsFromICP();

            while(! mFormulasToEncode.empty()) {
                std::cout << "Formula " << mFormulasToEncode.front() << " encoded to BV:" << std::endl;
                const FormulaT& formulaToEncode = mFormulasToEncode.front();

                FormulasT blastedFormulas = blastConstraint(formulaToEncode.constraint());
                for(auto blastedFormula : blastedFormulas) {
                    std::cout << " - " << blastedFormula << std::endl;
                }
                for(auto blastedFormula : blastedFormulas) {
                    addFormulaToBV(blastedFormula, formulaToEncode);
                }
                mFormulasToEncode.pop_front();
            }

            std::cout << "Running BV solver." << std::endl;

            Answer bvAnswer = mpBVSolver->check();
            std::cout << "Answer from BV solver: " << (bvAnswer == False ? "False" : (bvAnswer == True ? "True" : "Unknown")) << std::endl;

            if(bvAnswer == True) {
                 mSolutionOrigin = SolutionOrigin::BV;
                 return True;
            }
        }

        // At this point, the restriction is unsatisfiable
        // (determined either by the ICP module or by the BV solver).
        // Call backend

        updateOutsideRestrictionConstraint(icpAnswer == Unknown);

        Answer backendAnswer = runBackends(_full);
        mSolutionOrigin = SolutionOrigin::BACKEND;

        if(backendAnswer == False) {
            getInfeasibleSubsets();
            // The infeasible subsets from the backend may include the "outside restriction"-contraint.
            // Merge this with infeasible subsets from ICP or BV solver.

            std::vector<FormulasT> infeasibleInRestriction;

            if(icpAnswer == False) {
                infeasibleInRestriction.insert(infeasibleInRestriction.end(), mICP.infeasibleSubsets().begin(), mICP.infeasibleSubsets().end());
            } else {
                infeasibleInRestriction.insert(infeasibleInRestriction.end(), mpBVSolver->infeasibleSubsets().begin(), mpBVSolver->infeasibleSubsets().end());
            }
            assert(! infeasibleInRestriction.empty());

            std::vector<FormulasT> newInfeasibleSubsets;

            for(auto subsetIt=mInfeasibleSubsets.begin();subsetIt != mInfeasibleSubsets.end(); ) {
                auto& infeasibleSubset = *subsetIt;
                auto outsideRestriction = std::find(infeasibleSubset.begin(), infeasibleSubset.end(), mOutsideRestriction);

                if(outsideRestriction != infeasibleSubset.end()) {
                    infeasibleSubset.erase(outsideRestriction);
                    FormulasT newInfSubset(infeasibleSubset);
                    subsetIt = mInfeasibleSubsets.erase(subsetIt);

                    for(auto& infInRestriction : infeasibleInRestriction) {
                        FormulasT combinedInfSubset(newInfSubset);
                        combinedInfSubset.insert(combinedInfSubset.end(), infInRestriction.begin(), infInRestriction.end());
                        newInfeasibleSubsets.push_back(combinedInfSubset);
                    }
                } else {
                    ++subsetIt;
                }
            }

            mInfeasibleSubsets.insert(mInfeasibleSubsets.end(), newInfeasibleSubsets.begin(), newInfeasibleSubsets.end());
        }

        return backendAnswer;
    }

    bool IntBlastModule::reblastingNeeded(const BlastedPoly& _previousBlasting, const IntegerInterval& _interval, bool _linear) const
    {
        if(_previousBlasting.isConstant()) {
            return ! _interval.isPointInterval() || _interval.lower() != _previousBlasting.constant();
        }

        const BlastedType previousType = _previousBlasting.term().type();

        if(previousType.hasOffset() && ! _linear) {
            return true;
        }

        // Here we might choose different strategies.
        // For now, do a reblasting only if the new and the previous interval are disjoint.
        return ! previousType.bounds().intersectsWith(_interval);
    }

    void IntBlastModule::unblastVariable(const carl::Variable& _variable)
    {
        removeBoundRestrictionsFromICP(_variable);

        // Remove all blastings of polynomes in which _variable occurs
        auto polyIt = mPolyBlastings.begin();
        while(polyIt != mPolyBlastings.end()) {
            if(polyIt->first.has(_variable)) {
                polyIt = mPolyBlastings.erase(polyIt);
            } else {
                ++polyIt;
            }
        }

        // Remove all blastings of constraints in which _variable occurs
        auto constrIt = mConstrBlastings.begin();
        while(constrIt != mConstrBlastings.end()) {
            if(constrIt->first.lhs().has(_variable)) {
                constrIt = mConstrBlastings.erase(constrIt);
            } else {
                ++constrIt;
            }
        }
    }

    void IntBlastModule::blastVariable(const carl::Variable& _variable, const IntegerInterval& _interval, bool _allowOffset)
    {
        Poly variablePoly(_variable);
        if(_interval.isPointInterval()) {
            mPolyBlastings[variablePoly] = BlastedPoly(_interval.lower());
        }

        std::size_t maxWidth = 8; // TODO: Extract to a constant/setting

        // If interval is unbounded:
        //   Start with no offset, signed, maximum width (tempType)
        //     If offset is not allowed
        //       Remove sign if interval is semi-positive
        //     Else:
        //       If lower bound of interval is higher than tempType's lower bound, shift range using offset and remove sign
        //       (similar for upper bound)

        // If interval is bounded:
        //   If offset allowed:
        //     Lower bound as offset, width "as small as possible" (at most maximum width), unsigned
        //   Else:
        //     Make signed iff interval not semipositive
        //     Width "as small as possible" (at most maximum width)

        BlastedType blastedType;

        if(_interval.lowerBoundType() == carl::BoundType::INFTY || _interval.upperBoundType() == carl::BoundType::INFTY) {
            if(! _allowOffset) {
                blastedType = BlastedType(maxWidth, ! _interval.isSemiPositive(), 0);
            } else {
                BlastedType tempType(maxWidth, true, 0);

                if(_interval.lowerBoundType() != carl::BoundType::INFTY && _interval.lower() > tempType.lowerBound()) {
                    blastedType = BlastedType(maxWidth, false, _interval.lower());
                } else if(_interval.upperBoundType() != carl::BoundType::INFTY && _interval.upper() < tempType.upperBound()) {
                    blastedType = BlastedType(maxWidth, false, _interval.upper() - (tempType.upperBound() - tempType.lowerBound()));
                }
            }
        } else {
            // interval is bounded
            if(_allowOffset) {
                std::size_t width = chooseWidth(_interval.upper() - _interval.lower(), maxWidth, false);
                blastedType = BlastedType(width, false, _interval.lower());
            } else {
                if(_interval.isSemiPositive()) {
                    std::size_t width = chooseWidth(_interval.upper(), maxWidth, false);
                    blastedType = BlastedType(width, false, 0);
                } else {
                    std::size_t widthForUpper = chooseWidth(_interval.upper(), maxWidth, true);
                    std::size_t widthForLower = chooseWidth(_interval.lower(), maxWidth, true);
                    blastedType = BlastedType(std::max(widthForUpper, widthForLower), true, 0);
                }
            }
        }

        addBoundRestrictionsToICP(_variable, blastedType);

        mPolyBlastings[variablePoly] = BlastedPoly(BlastedTerm(blastedType));
    }

    void IntBlastModule::addBoundRestrictionsToICP(carl::Variable _variable, const BlastedType& blastedType)
    {
        addFormulaToICP(FormulaT(ConstraintT(_variable, carl::Relation::GEQ, blastedType.lowerBound())), mConstraintFromBounds);
        addFormulaToICP(FormulaT(ConstraintT(_variable, carl::Relation::LEQ, blastedType.upperBound())), mConstraintFromBounds);
    }

    void IntBlastModule::removeBoundRestrictionsFromICP(carl::Variable _variable)
    {
        auto& blastedVariable = mPolyBlastings.at(Poly(_variable));

        if(! blastedVariable.isConstant()) {
            const BlastedType& blastedType = blastedVariable.term().type();

            removeFormulaFromICP(FormulaT(ConstraintT(_variable, carl::Relation::GEQ, blastedType.lowerBound())), mConstraintFromBounds);
            removeFormulaFromICP(FormulaT(ConstraintT(_variable, carl::Relation::LEQ, blastedType.upperBound())), mConstraintFromBounds);
        }
    }

    std::size_t IntBlastModule::chooseWidth(const Integer& _numberToCover, std::size_t _maxWidth, bool _signed) const
    {
        assert(_numberToCover >= 0 || _signed);
        std::size_t width = 1;
        carl::Interval<Integer> interval(Integer(_signed ? -1 : 0), Integer(_signed ? 0 : 1));

        while((width < _maxWidth || _maxWidth == 0) && ! interval.contains(_numberToCover)) {
            ++width;
            interval.setLower(interval.lower() * 2);
            interval.setUpper((interval.upper()+1)*2 - 1);
        }
        return width;
    }

    void IntBlastModule::updateBoundsFromICP()
    {
        // TODO: This is not very incremental
        for(const FormulaT formula : mProcessedFormulasFromICP) {
            mBoundsInRestriction.removeBound(formula.constraint(), formula);
        }
        mProcessedFormulasFromICP.clear();
        for(ModuleInput::const_iterator fwo=mICP.rPassedFormula().begin(); fwo != mICP.rPassedFormula().end(); fwo++) {
            mBoundsInRestriction.addBound(fwo->formula().constraint(), fwo->formula());
            mProcessedFormulasFromICP.push_back(fwo->formula());
        }
    }

    void IntBlastModule::updateOutsideRestrictionConstraint(bool _includeSubstitutes)
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

        if(_includeSubstitutes) {
            auto& icpBounds = mBoundsInRestriction.getEvalIntervalMap();

            for(auto& polyWithOrigins : mSubstitutedPolys) {
                const Poly& poly = polyWithOrigins.element();

                // Compare "natural" bounds (bounds from ICP) to encoding bounds
                // (bounds from BV encodings).
                // Usually, the encoding bounds contain the natural bounds.
                // However, due to incrementality, the natural bounds may broaden
                // after the corresponding encoding bounds have been set. In this case,
                // we need to add further constraints to the backend.

                auto& blastedPoly = mPolyBlastings.at(poly);
                auto& substitute = mSubstitutes.at(poly);

                Integer blastedLowerBound = (blastedPoly.isConstant() ? blastedPoly.constant() : blastedPoly.term().type().lowerBound());
                Integer blastedUpperBound = (blastedPoly.isConstant() ? blastedPoly.constant() : blastedPoly.term().type().upperBound());
                auto icpBoundsIt = icpBounds.find(substitute);

                if(icpBoundsIt == icpBounds.end() || getNum(icpBoundsIt->second).contains(blastedLowerBound - 1)) {
                    // poly < blastedLowerBound  <=>  poly - blastedLowerBound < 0
                    outsideConstraints.push_back(FormulaT(ConstraintT(poly - Poly(blastedLowerBound), carl::Relation::LESS)));
                }

                if(icpBoundsIt == icpBounds.end() || getNum(icpBoundsIt->second).contains(blastedUpperBound + 1)) {
                    // poly > blastedUpperBound  <=>  poly - blastedUpperBound > 0
                    outsideConstraints.push_back(FormulaT(ConstraintT(poly - Poly(blastedUpperBound), carl::Relation::GREATER)));
                }
            }
        }

        FormulaT newOutsideConstraint(carl::FormulaType::OR, outsideConstraints);

        if(mOutsideRestriction != newOutsideConstraint) {
            // This is a hack. We need a non-const iterator to the old passed constraint,
            // so we retrieve it by inserting the constraint (a possibly second time) before.
            auto oldFormulaInPassedFormula = addSubformulaToPassedFormula(mOutsideRestriction, mOutsideRestrictionOrigin);
            removeOrigin(oldFormulaInPassedFormula.first, mOutsideRestrictionOrigin);
        }
        addSubformulaToPassedFormula(newOutsideConstraint, mOutsideRestrictionOrigin);
        mOutsideRestriction = newOutsideConstraint;
    }

    void IntBlastModule::addFormulaToICP(const FormulaT& _formula, const FormulaT& _origin)
    {
        std::cout << "-[ICP+]-> " << _formula << std::endl;
        auto insertionResult = mpICPInput->add(_formula, _origin);

        if(insertionResult.second) {
            mICP.inform(_formula);
            mICP.add(insertionResult.first);
        }
    }

    void IntBlastModule::addConstraintToICP(FormulaT _formula)
    {
        // First, add the formula itself to ICP
        addFormulaToICP(_formula, _formula);

        // Now we create a substitute for every node of the constraint tree of _formula
        // (except for the root, variable nodes and constant nodes)
        // in order to receive bounds from ICP for these expressions

        const ConstraintT& constraint = _formula.constraint();
        ConstrTree constraintTree(constraint);

        // Walk through the ConstraintTree in a breadth-first search
        std::list<const PolyTree*> nodesForSubstitution;
        nodesForSubstitution.push_back(&(constraintTree.left()));
        nodesForSubstitution.push_back(&(constraintTree.right()));

        while(! nodesForSubstitution.empty()) {
            const PolyTree& currentPoly = *(nodesForSubstitution.front());
            nodesForSubstitution.pop_front();

            if(currentPoly.type() == PolyTree::Type::SUM || currentPoly.type() == PolyTree::Type::PRODUCT) {
                // Find or create new substitute for the polynomial
                carl::Variable substitute;

                auto substituteLookup = mSubstitutes.find(currentPoly.poly());
                if(substituteLookup != mSubstitutes.end()) {
                    substitute = substituteLookup->second;
                } else {
                    substitute = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_INT);
                    mSubstitutes[currentPoly.poly()] = substitute;
                }

                // pass "substitute_variable = polynome" equation to ICP
                // (normalized: polynome - substitute_variable = 0)
                Poly polyMinusSubstitute(currentPoly.poly());
                polyMinusSubstitute -= substitute;
                FormulaT constraintForICP(polyMinusSubstitute, carl::Relation::EQ);

                addFormulaToICP(constraintForICP, _formula);

                // Remember that the polynome originates from _formula
                mSubstitutedPolys.add(currentPoly.poly(), _formula);

                // Schedule left and right subtree of current PolyTree
                // for being visited in the breadth-first search
                nodesForSubstitution.push_back(&(currentPoly.left()));
                nodesForSubstitution.push_back(&(currentPoly.right()));
            }
        }
    }

    void IntBlastModule::removeFormulaFromICP(const FormulaT& _formula, const FormulaT& _origin)
    {
        auto formulaInInput = mpICPInput->find(_formula);
        if(formulaInInput != mpICPInput->end()) {
            if(mpICPInput->removeOrigin(formulaInInput, _origin)) {
                mICP.remove(formulaInInput);
                mpICPInput->erase(formulaInInput);
            }
        }
    }

    void IntBlastModule::removeOriginFromICP(const FormulaT& _origin)
    {
        mSubstitutedPolys.removeOrigin(_origin);

        ModuleInput::iterator icpFormula = mpICPInput->begin();
        while(icpFormula != mpICPInput->end())
        {
            // Remove the given formula from the set of origins.
            if(mpICPInput->removeOrigin(icpFormula, _origin)) {
                mICP.remove(icpFormula);
                icpFormula = mpICPInput->erase(icpFormula);
            } else {
                ++icpFormula;
            }
        }
    }

    void IntBlastModule::addFormulaToBV(const FormulaT& _formula, const FormulaT& _origin)
    {
        std::cout << "-[BV +]-> " << _formula << std::endl;

        auto insertionResult = mpBVInput->add(_formula, _origin);
        if(insertionResult.second) { // The formula was fresh
            mpBVSolver->inform(_formula);
            mpBVSolver->add(_formula);
        }
    }

    void IntBlastModule::removeOriginFromBV(const FormulaT& _origin)
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

    void IntBlastModule::updateModelFromICP() const
    {
        clearModel();
        mICP.updateModel();
        mModel = mICP.model();
    }

    void IntBlastModule::updateModelFromBV() const
    {
        clearModel();
        const Model& bvModel = mpBVSolver->model();

        // Transfer all non-bitvector assignments
        for(auto& varAndValue : bvModel) {
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
                auto modelValue = carl::RealAlgebraicNumberNR<Rational>::create(blasting.constant(), false);
                mModel[ModelVariable(variable)] = ModelValue(modelValue);
            } else {
                const carl::BVTerm& blastedTerm = blasting.term().term();
                assert(blastedTerm.type() == carl::BVTermType::VARIABLE);
                const carl::BVVariable& bvVariable = blastedTerm.variable();
                const carl::BVValue& bvValue = mModel.at(ModelVariable(bvVariable)).asBVValue();
                Integer integerValue = decodeBVConstant(bvValue, blasting.term().type());
                auto modelValue = carl::RealAlgebraicNumberNR<Rational>::create(integerValue, false);
                mModel[ModelVariable(variable)] = ModelValue(modelValue);
            }
        }
    }

    IntBlastModule::IntegerInterval IntBlastModule::getNum(const RationalInterval& _interval) const
    {
        return IntegerInterval(
            carl::getNum(_interval.lower()), _interval.lowerBoundType(),
            carl::getNum(_interval.upper()), _interval.upperBoundType()
        );
    }
}