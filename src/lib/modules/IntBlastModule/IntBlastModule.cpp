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
    mICPInput(new ModuleInput()),
    mICPFoundAnswer( vector< std::atomic_bool* >( 1, new std::atomic_bool( false ) ) ),
    mICPRuntimeSettings(new RuntimeSettings()),
    mICP(MT_ICPModule, mICPInput, mICPRuntimeSettings, mICPFoundAnswer),
    mBVSolver(new BVSolver()),
    mLastSolutionFoundByBlasting(false),
    mBlastings(),
    mSubstitutes()
    {
        smtrat::addModules( mBVSolver );
        // TODO: Do we have to do some more initialization stuff here? Settings?

        std::cout << "IBM: initialization" << std::endl;
    }

    /**
     * Destructor.
     */

    IntBlastModule::~IntBlastModule()
    {
        while( !mICPFoundAnswer.empty() )
        {
            std::atomic_bool* toDel = mICPFoundAnswer.back();
            mICPFoundAnswer.pop_back();
            delete toDel;
        }
        mICPFoundAnswer.clear();
        delete mICPRuntimeSettings;
        delete mICPInput;
        delete mBVSolver;
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
        std::cout << "IBM: addCore(" << _subformula->formula() << ")" << std::endl;
        const FormulaT& formula = _subformula->formula();
        if( formula.getType() == carl::FormulaType::CONSTRAINT ) {
            mBoundsFromInput.addBound( formula.constraint(), formula );
            createSubstitutes( formula );
            addSubformulaToICPFormula(formula, formula);
        }

        addReceivedSubformulaToPassedFormula(_subformula);
        return ! mBoundsFromInput.isConflicting();
    }

    void IntBlastModule::removeCore( ModuleInput::const_iterator _subformula )
    {
        std::cout << "IBM: removeCore(" << _subformula->formula() << ")" << std::endl;
        const FormulaT& formula = _subformula->formula();
        if( formula.getType() == carl::FormulaType::CONSTRAINT ) {
            mBoundsFromInput.removeBound( formula.constraint(), formula );
        }
    }

    void IntBlastModule::updateModel() const
    {
        mModel.clear();
        if( solverState() == True )
        {
            if(mLastSolutionFoundByBlasting)
            {
                // TODO: Your code.
            }
            else
            {
                getBackendsModel();
            }
        }
    }

    void IntBlastModule::createSubstitutes(const FormulaT& _formula)
    {
        if(_formula.getType() == carl::FormulaType::CONSTRAINT)
        {
            createSubstitutes(_formula.constraint().lhs());
        }
    }

    void IntBlastModule::createSubstitutes(const Poly& _poly)
    {
        std::list<Poly> polysToSubstitute;
        Poly polyWithoutConstantPart(_poly);
        polyWithoutConstantPart -= polyWithoutConstantPart.constantPart();
        polysToSubstitute.push_back(polyWithoutConstantPart);

        while(! polysToSubstitute.empty()) {
            const Poly& currentPoly = polysToSubstitute.front();
            PolyDecomposition decomposition = decompose(currentPoly);

            if(decomposition.type() == PolyDecomposition::Type::VARIABLE) {
                std::cout << "* " << currentPoly << " is a variable leaf (" << decomposition.variable() << ")" << std::endl;
            } else if(decomposition.type() == PolyDecomposition::Type::CONSTANT) {
                std::cout << "* " << currentPoly << " is a constant leaf (" << decomposition.constant() << ")" << std::endl;
            } else {
                std::cout << "* " << currentPoly << " equals ";
                std::cout << decomposition.left();
                std::cout << (decomposition.type() == PolyDecomposition::Type::SUM ? " + " : " * ");
                std::cout << decomposition.right() << std::endl;
            }

            if(decomposition.type() == PolyDecomposition::Type::SUM || decomposition.type() == PolyDecomposition::Type::PRODUCT) {
                if(createSubstitute(currentPoly)) {
                    polysToSubstitute.push_back(decomposition.left());
                    polysToSubstitute.push_back(decomposition.right());
                }
            }
            polysToSubstitute.pop_front();
        }
    }

    bool IntBlastModule::createSubstitute(const Poly& _poly)
    {
        std::cout << "createSubstitute(" << _poly << ")";
        auto substituteLookup = mSubstitutes.find(_poly);
        if(substituteLookup != mSubstitutes.end()) {
            std::cout << " - old." << std::endl;
            return false; // substituteLookup->second;
        }
        std::cout << " - FRESH." << std::endl;
        carl::Variable freshSubstitute = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_INT);
        mSubstitutes[_poly] = freshSubstitute;

        // pass equation to ICP
        Poly polyMinusSubstitute(_poly);
        polyMinusSubstitute -= freshSubstitute;
        addSubformulaToICPFormula(FormulaT(polyMinusSubstitute, carl::Relation::EQ), FormulaT()); // TODO: Correct origin
        return true; // freshSubstitute;
    }

    PolyDecomposition IntBlastModule::decompose(const Poly& _polynomial) const
    {
        Poly poly(_polynomial);
        poly.makeOrdered();

        std::size_t nrTerms = poly.nrTerms();

        if(nrTerms == 0) {
            return PolyDecomposition(PolyDecomposition::Type::CONSTANT, 0);
        }
        if(nrTerms > 1) {
            auto lastTerm = poly.rbegin();
            return PolyDecomposition(PolyDecomposition::Type::SUM, poly - *lastTerm, Poly(*lastTerm));
        }

        const TermT& term = poly[0];
        Rational coeff = term.coeff();

        if(term.isConstant()) {
            return PolyDecomposition(PolyDecomposition::Type::CONSTANT, coeff);
        }

        const carl::Monomial::Arg monomial = term.monomial();

        if(! carl::isOne(coeff)) {
            return PolyDecomposition(PolyDecomposition::Type::PRODUCT, Poly(coeff), Poly(monomial));
        }

        auto variableAndExponent = *(monomial->begin());

        if(monomial->nrVariables() > 1) {
            carl::Monomial::Arg head = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second);
            carl::Monomial::Arg tail = monomial->dropVariable(variableAndExponent.first);
            return PolyDecomposition(PolyDecomposition::Type::PRODUCT, Poly(head), Poly(tail));
        }

        if(variableAndExponent.second > 1) {
            carl::Monomial::Arg remainder = carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second - 1);
            return PolyDecomposition(PolyDecomposition::Type::PRODUCT, Poly(remainder), Poly(variableAndExponent.first));
        }

        return PolyDecomposition(PolyDecomposition::Type::VARIABLE, variableAndExponent.first);
    }

    void IntBlastModule::blastSubstitutes()
    {
        FormulasT blastedFormulas;

        for(auto polyAndSubstitute : mSubstitutes) {
            std::cout << "Blasting: " << polyAndSubstitute.first << std::endl;
            PolyDecomposition decomposition = decompose(polyAndSubstitute.first);
            BlastedTerm blastedTerm = blastedTermForPolynomial(polyAndSubstitute.first);

            if(decomposition.type() == PolyDecomposition::Type::CONSTANT) {
                // TODO: Is this whole if-case actually needed? I do not think so.
                carl::BVValue constant(blastedTerm.type().width(), carl::getNum(decomposition.constant()));
                carl::BVTerm constTerm(carl::BVTermType::CONSTANT, constant);
                carl::BVConstraint constr = carl::BVConstraint::create(carl::BVCompareRelation::EQ, blastedTerm.term(), constTerm);
                blastedFormulas.insert(FormulaT(constr));

                for(auto blaFo : blastedFormulas) {
                    std::cout << "-> [Subs] " << blaFo << std::endl;
                }
            } else if(decomposition.type() == PolyDecomposition::Type::VARIABLE) {
                // nothing to do here
            } else {
                const BlastedTerm& left = blastedTermForPolynomial(decomposition.left());
                const BlastedTerm& right = blastedTermForPolynomial(decomposition.right());

                if(decomposition.type() == PolyDecomposition::Type::SUM) {
                    blastSum(left, right, blastedTerm);
                } else {
                    assert(decomposition.type() == PolyDecomposition::Type::PRODUCT);
                    blastProduct(left, right, blastedTerm);
                }
            }
        }
    }

    const BlastedTerm& IntBlastModule::blastedTermForPolynomial(const Poly& _poly)
    {
        auto foundBlasting = mBlastings.find(_poly);

        if(foundBlasting != mBlastings.end()) {
            return foundBlasting->second;
        }

        BlastedTerm output;

        PolyDecomposition decomposition = decompose(_poly);

        if(decomposition.type() == PolyDecomposition::Type::CONSTANT) {
            BlastedType blastedType = chooseBlastedType(DoubleInterval(decomposition.constant(), decomposition.constant()));
            carl::BVValue constValue(blastedType.width(), carl::getNum(decomposition.constant()));
            output = BlastedTerm(blastedType, carl::BVTerm(carl::BVTermType::CONSTANT, constValue));
        } else {
            carl::Variable variable;

            if(decomposition.type() == PolyDecomposition::Type::VARIABLE) {
                variable = decomposition.variable();
            } else {
                variable = mSubstitutes[_poly];
            }

            const EvalDoubleIntervalMap& icpBounds = mBoundsInRestriction.getIntervalMap();
            auto foundBound = icpBounds.find(variable);
            if(foundBound != icpBounds.end()) {
                output = BlastedTerm(chooseBlastedType(foundBound->second));
            } else {
                std::cout << "Unbounded :(" << std::endl;
                assert(false);
            }
        }

        mBlastings[_poly] = output;
        return mBlastings[_poly];
    }

    void IntBlastModule::blastSum(const BlastedTerm& _summand1, const BlastedTerm& _summand2, const BlastedTerm& _sum)
    {
        FormulasT blastedFormulas;

        BlastedTerm safeSum(BlastedType::forSum(_summand1.type(), _summand2.type()));

        carl::BVTerm bvSummand1((_summand1.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                _summand1.term(),
                                safeSum.type().width() - _summand1.type().width());
        carl::BVTerm bvSummand2((_summand2.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                _summand2.term(),
                                safeSum.type().width() - _summand2.type().width());

        blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                   carl::BVTerm(carl::BVTermType::ADD, bvSummand1, bvSummand2),
                                                                   safeSum.term())));
        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Sum ] " << blaFo << std::endl;
        }
        safeCast(safeSum, _sum);
    }

    void IntBlastModule::blastProduct(const BlastedTerm& _factor1, const BlastedTerm& _factor2, const BlastedTerm& _product)
    {
        FormulasT blastedFormulas;

        BlastedTerm safeProduct(BlastedType::forProduct(_factor1.type(), _factor2.type()));

        carl::BVTerm bvFactor1(_factor1.term());
        if(safeProduct.type().width() > _factor1.type().width()) {
            bvFactor1 = carl::BVTerm((_factor1.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                     _factor1.term(),
                                     safeProduct.type().width() - _factor1.type().width());
        }

        carl::BVTerm bvFactor2(_factor1.term());
        if(safeProduct.type().width() > _factor2.type().width()) {
            bvFactor2 = carl::BVTerm((_factor2.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                     _factor2.term(),
                                     safeProduct.type().width() - _factor2.type().width());
        }

        blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                   carl::BVTerm(carl::BVTermType::MUL, bvFactor1, bvFactor2),
                                                                   safeProduct.term())));

        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Prod] " << blaFo << std::endl;
        }
        safeCast(safeProduct, _product);
    }

    void IntBlastModule::safeCast(const BlastedTerm& _from, const BlastedTerm& _to)
    {
        FormulasT blastedFormulas;

        // cast to desired representation
        if(_to.type().width() > _from.type().width()) {
            // unlikely...
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       carl::BVTerm((_from.type().isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U), _from.term(), _to.type().width() - _from.type().width()),
                                                                       _to.term())));
        } else if(_to.type().width() == _from.type().width()) {
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       _from.term(),
                                                                       _to.term())));
        } else {
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       carl::BVTerm(carl::BVTermType::EXTRACT, _from.term(), _to.type().width()-1, 0),
                                                                       _to.term())));
        }

        // ensure safety
        if(_to.type().isSigned()) {
            // If bits have been removed, they must equal the msb of _to
            if(_to.type().width() < _from.type().width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, _from.term(), _from.type().width()-1, _to.type().width()),
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, _from.term(), _from.type().width()-2, _to.type().width()-1))));
            }
            // If _from is unsigned, _to must be non-negative (i.e. the msb of _to must be zero)
            // (this check can be skipped if _to is wider than _from - in this case we had zero extension)
            if(_to.type().width() <= _from.type().width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, _to.term(), _to.type().width()-1, _to.type().width()-1),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(1, 0)))));
            }
        } else { // ! _to.isSigned()
            // If bits have been removed, they must be zero
            if(_to.type().width() < _from.type().width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, _from.term(), _from.type().width()-1, _to.type().width()),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(_from.type().width() - _to.type().width(), 0)))));
            }
            // If _from is unsigned, it must be non-negative
            if(! _from.type().isSigned()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, _from.term(), _from.type().width()-1, _from.type().width()-1),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(1, 0)))));
            }
        }

        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Cast] " << blaFo << std::endl;
        }
    }

    void IntBlastModule::addSubformulaToICPFormula(const FormulaT& _formula, const FormulaT& _origin)
    {
        mICP.inform(_formula); // TODO: Use result somehow?
        auto insertion = mICPInput->add(_formula, _origin);

        if(insertion.second)
        {
            mICP.add(insertion.first);
        }
    }

    void IntBlastModule::blastInputVariables()
    {
        std::cout << "IBM: blastInputVariables()" << std::endl;
        carl::Variables newVariables;

        for(ModuleInput::const_iterator formula=firstUncheckedReceivedSubformula(); formula != rReceivedFormula().end(); ++formula)
        {
            formula->formula().integerValuedVars(newVariables);
        }

        if(! newVariables.empty())
        {
            const EvalDoubleIntervalMap& passedBounds = mBoundsFromInput.getIntervalMap();

            for(const carl::Variable& variable : newVariables)
            {
                Poly varPoly(variable);
                auto previousBlasting = mBlastings.find(varPoly);
                if(previousBlasting == mBlastings.end())
                {
                    std::cout << "Setting blasting type for " << variable << std::endl;
                    DoubleInterval varInterval;

                    auto varBounds = passedBounds.find(variable);
                    if(varBounds != passedBounds.end())
                    {
                        varInterval = varBounds->second;
                    }

                    std::cout << "Natural interval: " << varInterval << std::endl;
                    mBlastings[varPoly] = BlastedTerm(chooseBlastedType(varInterval, 8)); // TODO: Refactor 8 to a constant / setting

                    BlastedTerm& blastedTerm = mBlastings[varPoly];
                    std::cout << "Encoding by " << blastedTerm.term() << " (width: " << blastedTerm.type().width() << ", " << (blastedTerm.type().isSigned() ? "signed" : "unsigned") << ") - range [" << blastedTerm.type().lowerBound() << "," << blastedTerm.type().upperBound() << "]" << std::endl;

                    ConstraintT lowerBoundConstr(variable, carl::Relation::GEQ, blastedTerm.type().lowerBound());
                    ConstraintT upperBoundConstr(variable, carl::Relation::LEQ, blastedTerm.type().upperBound());

                    addSubformulaToICPFormula(FormulaT(lowerBoundConstr), FormulaT()); // TODO: correct origin
                    addSubformulaToICPFormula(FormulaT(upperBoundConstr), FormulaT()); // TODO: correct origin
                }
            }
        }
    }

    BlastedType IntBlastModule::chooseBlastedType(const DoubleInterval _interval, std::size_t _maxWidth) const
    {
        std::cout << "Choosing blasted type for interval " << _interval << ", max width " << _maxWidth << std::endl;
        std::size_t width = _maxWidth;
        bool makeSigned = true;

        if(_interval.isSemiPositive())
        {
            makeSigned = false;
        }

        if(_interval.lowerBoundType() != carl::BoundType::INFTY && _interval.upperBoundType() != carl::BoundType::INFTY)
        {
            // Reduce width if interval is small enough
            std::size_t smallWidth = 1;
            DoubleInterval smallInterval((makeSigned ? -1 : 0), (makeSigned ? 0 : 1));

            while((smallWidth < _maxWidth || _maxWidth == 0) && ! smallInterval.contains(_interval)) {
                ++smallWidth;
                smallInterval.setLower(smallInterval.lower() * 2);
                smallInterval.setUpper((smallInterval.upper()+1)*2 - 1);
            }
            width = smallWidth;
        }

        assert(width > 0);

        return BlastedType(width, makeSigned);
    }

    Answer IntBlastModule::checkCore( bool _full )
    {
        std::cout << "IBM: checkCore()" << std::endl;
        blastInputVariables();

        std::cout << "Blastings:" << std::endl;
        for(auto blaPa : mBlastings) {
            std::cout << blaPa.first << " --> " << blaPa.second.term() << " (width " << blaPa.second.type().width() << ")" << std::endl;
        }

        std::cout << "Substitutes:" << std::endl;
        for(auto substi : mSubstitutes) {
            std::cout << substi.first << " --> " << substi.second << std::endl;
        }



        Answer icpAnswer = mICP.check();
        std::cout << "icpAnswer: " << (icpAnswer == True ? "True" : (icpAnswer == False ? "False" : "Unknown")) << std::endl;

        if(icpAnswer == True) {
            return True;
            // TODO: Remember to receive model from mICP
        } else if(icpAnswer != False) {
            // TODO: This is not very incremental
            for(const FormulaT formula : mProcessedFormulasFromICP) {
                mBoundsInRestriction.removeBound(formula.constraint(), formula);
            }
            mProcessedFormulasFromICP.clear();
            for(ModuleInput::const_iterator fwo=mICP.rPassedFormula().begin(); fwo != mICP.rPassedFormula().end(); fwo++) {
                mBoundsInRestriction.addBound(fwo->formula().constraint(), fwo->formula());
                mProcessedFormulasFromICP.insert(fwo->formula());
            }

            /*
            std::cout << "Variable bounds from ICP:" << std::endl;

            const EvalDoubleIntervalMap& icpBounds = mBoundsInRestriction.getIntervalMap();

            for(auto polyAndSubstitute : mSubstitutes) {
                std::cout << polyAndSubstitute.first << " (" << polyAndSubstitute.second << "): ";

                auto foundBound = icpBounds.find(polyAndSubstitute.second);
                if(foundBound != icpBounds.end()) {
                    std::cout << *foundBound << std::endl;
                    Poly substPoly(polyAndSubstitute.second);
                    mBlastings[substPoly] = BlastedTerm(chooseBlastedType(foundBound->second));

                    BlastedTerm& blastedTerm = mBlastings[substPoly];
                    std::cout << "--> " << blastedTerm.term() << " (width: " << blastedTerm.type().width() << ", " << (blastedTerm.type().isSigned() ? "signed" : "unsigned") << ") - range [" << blastedTerm.type().lowerBound() << "," << blastedTerm.type().upperBound() << "]" << std::endl;
                } else {
                    std::cout << "Unbounded :(" << std::endl;
                }
            } */

            std::cout << "Blasting substitutes!" << std::endl;
            blastSubstitutes();

            auto receivedSubformula = firstUncheckedReceivedSubformula();
            while(receivedSubformula != rReceivedFormula().end())
            {
                const FormulaWithOrigins& fwo = *receivedSubformula;
                const FormulaT& formula = fwo.formula();

                /* const FormulaT& blastedFormula = blast(formula);

                mBVSolver->inform(blastedFormula);
                mBVSolver->add(blastedFormula); */

                ++receivedSubformula;
            }
        }

        // }
        // TODO: Do the blasting

        // BV solver was unable to derive an answer.
        // Fall back to backend.
        mLastSolutionFoundByBlasting = false;
        Answer backendAnswer = runBackends(_full);
        if(backendAnswer == False)
        {
            getInfeasibleSubsets();
        }

        return backendAnswer;
    }
}