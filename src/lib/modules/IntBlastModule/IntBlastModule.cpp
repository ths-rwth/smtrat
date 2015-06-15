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
    mBlastingParameters(),
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

        return;

        std::cout << "Back to normal..." << std::endl;

        Poly currentPoly(_poly);
        currentPoly -= currentPoly.constantPart();
        currentPoly.makeOrdered();

        while(! currentPoly.isZero()) {
            auto lastTerm = currentPoly.rbegin();
            assert(lastTerm != currentPoly.rend());
            createSubstitutes(*lastTerm);
            createSubstitute(currentPoly);
            currentPoly -= *lastTerm;
        }
    }

    void IntBlastModule::createSubstitutes(const TermT& _term)
    {
        const carl::Monomial::Arg monomial = _term.monomial();
        assert(! monomial->isConstant());

        Poly currentPoly(1);

        for( auto variableAndExponent : *monomial ) {
            createSubstitutes(variableAndExponent.first, variableAndExponent.second);
            currentPoly *= carl::MonomialPool::getInstance().create(variableAndExponent.first, variableAndExponent.second);
            createSubstitute(currentPoly);
        }

        assert(! currentPoly.isConstant());

        Poly termPoly(_term);
        createSubstitute(termPoly);
    }

    void IntBlastModule::createSubstitutes(const carl::Variable::Arg variable, carl::exponent exponent)
    {
        for(carl::exponent exp=exponent;exp>=1;--exp) {
            Poly lookupPoly(carl::MonomialPool::getInstance().create(variable, exp));

            if(exp == 1) {
                mSubstitutes[lookupPoly] = variable;
            } else {
                createSubstitute(lookupPoly);
            }
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
            BlastingParameters blastingParams = mBlastingParameters[polyAndSubstitute.second];

            if(decomposition.type() == PolyDecomposition::Type::CONSTANT) {
                carl::BVValue constant(blastingParams.width(), carl::getNum(decomposition.constant()));
                carl::BVTerm varTerm(carl::BVTermType::VARIABLE, blastingParams.variable());
                carl::BVTerm constTerm(carl::BVTermType::CONSTANT, constant);
                carl::BVConstraint constr = carl::BVConstraint::create(carl::BVCompareRelation::EQ, varTerm, constTerm);
                blastedFormulas.insert(FormulaT(constr));

                for(auto blaFo : blastedFormulas) {
                    std::cout << "-> [Subs] " << blaFo << std::endl;
                }
            } else if(decomposition.type() == PolyDecomposition::Type::VARIABLE) {
                // nothing to do here
            } else {
                BlastingParameters& left = mBlastingParameters[mSubstitutes[decomposition.left()]];
                BlastingParameters& right = mBlastingParameters[mSubstitutes[decomposition.right()]];

                if(decomposition.type() == PolyDecomposition::Type::SUM) {
                    blastSum(left, right, blastingParams);
                } else {
                    assert(decomposition.type() == PolyDecomposition::Type::PRODUCT);
                    blastProduct(left, right, blastingParams);
                }
            }
        }
    }

    void IntBlastModule::blastSum(const BlastingParameters& _summand1, const BlastingParameters& _summand2, const BlastingParameters& _sum)
    {
        FormulasT blastedFormulas;

        // determine safe representation of result
        std::size_t width1 = _summand1.width();
        std::size_t width2 = _summand2.width();
        bool anySigned = (_summand1.isSigned() || _summand2.isSigned());

        if(_summand1.isSigned() != _summand2.isSigned()) {
            if(_summand1.isSigned()) {
                ++width2;
            } else {
                ++width1;
            }
        }

        std::size_t safeWidth = ((width1 > width2) ? width2 : width1) + 1;

        BlastingParameters safeSum = BlastingParameters::createWithVariable(safeWidth, anySigned);

        carl::BVTerm bvSummand1((_summand1.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                carl::BVTerm(carl::BVTermType::VARIABLE, _summand1.variable()),
                                safeWidth - _summand1.width());
        carl::BVTerm bvSummand2((_summand2.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                carl::BVTerm(carl::BVTermType::VARIABLE, _summand2.variable()),
                                safeWidth - _summand2.width());

        blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                   carl::BVTerm(carl::BVTermType::ADD, bvSummand1, bvSummand2),
                                                                   carl::BVTerm(carl::BVTermType::VARIABLE, safeSum.variable()))));
        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Sum ] " << blaFo << std::endl;
        }
        safeCast(safeSum, _sum);
    }

    void IntBlastModule::blastProduct(const BlastingParameters& _factor1, const BlastingParameters& _factor2, const BlastingParameters& _product)
    {
        FormulasT blastedFormulas;

        // determine safe representation of result
        bool anySigned = (_factor1.isSigned() || _factor2.isSigned());
        std::size_t safeWidth = _factor1.width() + _factor2.width() - (_factor1.isSigned() && _factor2.isSigned() ? 1 : 0);

        BlastingParameters safeProduct = BlastingParameters::createWithVariable(safeWidth, anySigned);

        carl::BVTerm bvFactor1(carl::BVTermType::VARIABLE, _factor1.variable());
        if(safeWidth > _factor1.width()) {
            bvFactor1 = carl::BVTerm((_factor1.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                     carl::BVTerm(carl::BVTermType::VARIABLE, _factor1.variable()),
                                     safeWidth - _factor1.width());
        }

        carl::BVTerm bvFactor2(carl::BVTermType::VARIABLE, _factor2.variable());
        if(safeWidth > _factor2.width()) {
            bvFactor2 = carl::BVTerm((_factor2.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U),
                                     carl::BVTerm(carl::BVTermType::VARIABLE, _factor2.variable()),
                                     safeWidth - _factor2.width());
        }

        blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                   carl::BVTerm(carl::BVTermType::MUL, bvFactor1, bvFactor2),
                                                                   carl::BVTerm(carl::BVTermType::VARIABLE, safeProduct.variable()))));

        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Prod] " << blaFo << std::endl;
        }
        safeCast(safeProduct, _product);
    }

    void IntBlastModule::safeCast(const BlastingParameters& _from, const BlastingParameters& _to)
    {
        FormulasT blastedFormulas;

        // cast to desired representation
        if(_to.width() > _from.width()) {
            // unlikely...
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       carl::BVTerm((_from.isSigned() ? carl::BVTermType::EXT_S : carl::BVTermType::EXT_U), carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _to.width() - _from.width()),
                                                                       carl::BVTerm(carl::BVTermType::VARIABLE, _to.variable()))));
        } else if(_to.width() == _from.width()) {
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()),
                                                                       carl::BVTerm(carl::BVTermType::VARIABLE, _to.variable()))));
        } else {
            blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                       carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _to.width()-1, 0),
                                                                       carl::BVTerm(carl::BVTermType::VARIABLE, _to.variable()))));
        }

        // ensure safety
        if(_to.isSigned()) {
            // If bits have been removed, they must equal the msb of _to
            if(_to.width() < _from.width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _from.width()-1, _to.width()),
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _from.width()-2, _to.width()-1))));
            }
            // If _from is unsigned, _to must be non-negative (i.e. the msb of _to must be zero)
            // (this check can be skipped if _to is wider than _from - in this case we had zero extension)
            if(_to.width() <= _from.width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _to.variable()), _to.width()-1, _to.width()-1),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(1, 0)))));
            }
        } else { // ! _to.isSigned()
            // If bits have been removed, they must be zero
            if(_to.width() < _from.width()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _from.width()-1, _to.width()),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(_from.width() - _to.width(), 0)))));
            }
            // If _from is unsigned, it must be non-negative
            if(! _from.isSigned()) {
                blastedFormulas.insert(FormulaT(carl::BVConstraint::create(carl::BVCompareRelation::EQ,
                                                                           carl::BVTerm(carl::BVTermType::EXTRACT, carl::BVTerm(carl::BVTermType::VARIABLE, _from.variable()), _from.width()-1, _from.width()-1),
                                                                           carl::BVTerm(carl::BVTermType::CONSTANT, carl::BVValue(1, 0)))));
            }
        }

        for(auto blaFo : blastedFormulas) {
            std::cout << "-> [Cast] " << blaFo << std::endl;
        }
    }

    /* FormulaT IntBlastModule::blast(const FormulaT& _formula)
    {
        if(_formula.getType() == carl::FormulaType::CONSTRAINT) {

        } else {
            return _formula;
        }
    } */

    /*void IntBlastModule::createMonomialSubstitutes(const FormulaT& _formula)
    {
        const ConstraintT& constraint = _formula.constraint();
        const Poly& poly = constraint.lhs();
        for( auto var : constraint.variables() )
        {
            if( var.getType() == carl::VariableType::VT_INT )
            {
                std::size_t degree = poly.degree(var);
                for(unsigned i=2;i<=degree;++i) {
                    carl::Monomial::Arg monomial = carl::MonomialPool::getInstance().create(var, i);
                    auto existingSubstitute = mSubstitutes.find(monomial);
                    if(existingSubstitute == mSubstitutes.end()) {
                        // create new substitute
                        carl::Variable substitute = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_INT);
                        mSubstitutes[monomial] = substitute;

                        // pass equation to ICP
                        Poly substitution({TermT(monomial), TermT(-1, carl::MonomialPool::getInstance().create(substitute, 1))});
                        addSubformulaToICPFormula(FormulaT(substitution, carl::Relation::EQ), _formula);
                    }
                }
            }
        }
    } */

    void IntBlastModule::addSubformulaToICPFormula(const FormulaT& _formula, const FormulaT& _origin)
    {
        mICP.inform(_formula); // TODO: Use result somehow?
        auto insertion = mICPInput->add(_formula, _origin);

        if(insertion.second)
        {
            mICP.add(insertion.first);
        }
    }

    void IntBlastModule::updateBlastingParameters()
    {
        std::cout << "IBM: updateBlastingParameters()" << std::endl;
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
                auto existingBlastingParameters = mBlastingParameters.find(variable);
                if(existingBlastingParameters == mBlastingParameters.end())
                {
                    std::cout << "Setting blasting parameters for " << variable << std::endl;
                    DoubleInterval varInterval;

                    auto varBounds = passedBounds.find(variable);
                    if(varBounds != passedBounds.end())
                    {
                        varInterval = varBounds->second;
                    }

                    std::cout << "Natural interval: " << varInterval << std::endl;
                    mBlastingParameters[variable] = chooseBlastingParameters(varInterval, 8); // TODO: Refactor 8 to a constant / setting

                    BlastingParameters& blastingParams = mBlastingParameters[variable];
                    std::cout << "Encoding by " << blastingParams.variable() << " (width: " << blastingParams.width() << ", " << (blastingParams.isSigned() ? "signed" : "unsigned") << ") - range [" << blastingParams.lowerBound() << "," << blastingParams.upperBound() << "]" << std::endl;

                    ConstraintT lowerBoundConstr(variable, carl::Relation::GEQ, blastingParams.lowerBound());
                    ConstraintT upperBoundConstr(variable, carl::Relation::LEQ, blastingParams.upperBound());

                    addSubformulaToICPFormula(FormulaT(lowerBoundConstr), FormulaT()); // TODO: correct origin
                    addSubformulaToICPFormula(FormulaT(upperBoundConstr), FormulaT()); // TODO: correct origin
                }
            }
        }
    }

    BlastingParameters IntBlastModule::chooseBlastingParameters(const DoubleInterval _interval, std::size_t _maxWidth) const
    {
        std::cout << "Choosing blasting parameters for interval " << _interval << ", max width " << _maxWidth << std::endl;
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

        return BlastingParameters::createWithVariable(width, makeSigned);
        // Create fresh bitvector variable
        /* carl::Variable var = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_BITVECTOR);
        carl::Sort bvSort = carl::SortManager::getInstance().getSort("BitVec", {width});
        carl::BVVariable bvVar(var, bvSort);

        return BlastingParameters(bvVar, makeSigned); */
    }

    Answer IntBlastModule::checkCore( bool _full )
    {
        std::cout << "IBM: checkCore()" << std::endl;
        updateBlastingParameters();

        std::cout << "Blasting parameters:" << std::endl;
        for(auto blaPa : mBlastingParameters) {
            std::cout << blaPa.first << " --> " << blaPa.second.variable() << " (width " << blaPa.second.width() << ")" << std::endl;
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

            std::cout << "Variable bounds from ICP:" << std::endl;

            const EvalDoubleIntervalMap& icpBounds = mBoundsInRestriction.getIntervalMap();

            for(auto polyAndSubstitute : mSubstitutes) {
                std::cout << polyAndSubstitute.first << " (" << polyAndSubstitute.second << "): ";

                auto foundBound = icpBounds.find(polyAndSubstitute.second);
                if(foundBound != icpBounds.end()) {
                    std::cout << *foundBound << std::endl;
                    mBlastingParameters[polyAndSubstitute.second] = chooseBlastingParameters(foundBound->second);
                    BlastingParameters& blastingParams = mBlastingParameters[polyAndSubstitute.second];
                    std::cout << "--> " << blastingParams.variable() << " (width: " << blastingParams.width() << ", " << (blastingParams.isSigned() ? "signed" : "unsigned") << ") - range [" << blastingParams.lowerBound() << "," << blastingParams.upperBound() << "]" << std::endl;
                } else {
                    std::cout << "Unbounded :(" << std::endl;
                }
            }

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