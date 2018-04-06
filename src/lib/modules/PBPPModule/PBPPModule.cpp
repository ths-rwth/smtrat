/**
 * @file PBPP.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#include "PBPPModule.h"

namespace smtrat
{

    template<class Settings>
        PBPPModule<Settings>::PBPPModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
            Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
            , mStatistics(Settings::moduleName)
#endif
            {
                checkFormulaAndApplyTransformationsCallback = std::bind(&PBPPModule<Settings>::checkFormulaAndApplyTransformations, this, std::placeholders::_1);
            }

    template<class Settings>
        PBPPModule<Settings>::~PBPPModule()
        {}

    template<class Settings>
        bool PBPPModule<Settings>::informCore( const FormulaT& )
        {
            return true; // This should be adapted according to your implementation.
        }

    template<class Settings>
        void PBPPModule<Settings>::init()
        {}

    template<class Settings>
        bool PBPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
        {
            // TODO double check objective stuff
            if (objective() != carl::Variable::NO_VARIABLE) {
                for (const auto& var: objectiveFunction().gatherVariables()) {
                    mVariablesCache.emplace(var, carl::freshBooleanVariable());
                }
            }

            FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaAndApplyTransformationsCallback);
            addSubformulaToPassedFormula(formula, _subformula->formula());
            return true;
        }

    template<class Settings>
        void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator )
        {

        }

    template<class Settings>
        void PBPPModule<Settings>::updateModel() const
        {
            mModel.clear();
            if( solverState() == Answer::SAT )
            {
                getBackendsModel();
            }
        }

    template<class Settings>
        Answer PBPPModule<Settings>::checkCore()
        {
            Answer ans = runBackends();
            if (ans == UNSAT) {
                generateTrivialInfeasibleSubset();
            }
            return ans;
        }

    template<class Settings>
        FormulaT PBPPModule<Settings>::checkFormulaAndApplyTransformations(const FormulaT& subformula) {
            SMTRAT_LOG_DEBUG("smtrat.pbc", "Got formula type " << subformula.getType());

            FormulaT formula;
            if (subformula.getType() == carl::FormulaType::PBCONSTRAINT) {
                // We get an old input Format. Instead of PBCONSTRAINT we would like to work
                // with CONSTRAINTs
                // Hence, for compatibility, we convert the Formula to the correct type.
                formula = convertPbConstraintToConstraintFormula(subformula);
            } else {
                // pass through.
                formula = subformula;
            }

            if(formula.getType() != carl::FormulaType::CONSTRAINT){
                return formula;
            }

            const ConstraintT& constraint = formula.constraint();
            if (!isPseudoBoolean(constraint)) { // eg an objective function
                return formula;
            }

            assertAssumptionsForTransformation(formula);

            // extract important information: lhs, rhs, hasRhs
            const Poly& lhs = constraint.lhs();
            const Rational rhs = constraint.constantPart();
            const carl::Relation relation = constraint.relation();

            // actually apply transformations
            if (Settings::use_rns_transformation){
                return checkFormulaTypeWithRNS(formula);
            } else if (Settings::use_card_transformation){
                return checkFormulaTypeWithCardConstr(formula);
            } else if (Settings::use_mixed_transformation){
                return checkFormulaTypeWithMixedConstr(formula);
            } else if (Settings::use_basic_transformation){
                return checkFormulaTypeBasic(formula);
            } else {
                return checkFormulaType(formula);
            }

            // IDEA apply more than one tranformation and take the one with most "gain"
            // however, we need a notion of gain first.

            assert(false);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::convertPbConstraintToConstraintFormula(const FormulaT& formula) {
            assert(formula.getType() == carl::FormulaType::PBCONSTRAINT);

            const PBConstraintT& pbConstraint = formula.pbConstraint();
            // extract the parts we are working with
            const std::vector<std::pair<Rational, carl::Variable>>& pbLhs = pbConstraint.getLHS();
            const Rational& rhs = pbConstraint.getRHS();

            Poly lhs;
            for (const auto& term : pbLhs) {
                auto it = mVariablesCache.find(term.second);
                if (it == mVariablesCache.end()) {
                    // We haven't seen this variable, yet. Create a new map entry for it.
                    mVariablesCache[term.second] = carl::freshBooleanVariable();
                }

                const carl::Variable& booleanVariable = mVariablesCache[term.second];
                lhs += Poly(term.first) * Poly(booleanVariable);
            }

            // the new constraint, based on the pbConstraint
            ConstraintT constraint(lhs - Poly(rhs), pbConstraint.getRelation());

            SMTRAT_LOG_INFO("smtrat.pbc", "converted PBConstraint " << pbConstraint
                    << " to arithmetic constraint "
                    << constraint);

            return FormulaT(constraint);
        }

    template<typename Settings>
        bool PBPPModule<Settings>::isPseudoBoolean(const ConstraintT& constraint) {
            for (const auto& term : constraint.lhs()) {
                std::set<carl::Variable> variables;
                term.gatherVariables(variables);
                for (const auto& var : variables) {
                    if (var.getType() != carl::VariableType::VT_BOOL) {
                        return false;
                    }
                }
            }

            return true;
        }

    template<class Settings>
        void PBPPModule<Settings>::assertAssumptionsForTransformation(const FormulaT& subformula) {
            assert(subformula.getType() == carl::FormulaType::CONSTRAINT);
            assert(isPseudoBoolean(subformula.constraint()));
            assert(subformula.constraint().relation() != carl::Relation::GEQ);
            assert(subformula.constraint().relation() != carl::Relation::GREATER);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaType(const FormulaT& inputFormula){
            const ConstraintT& constraint = inputFormula.constraint();
            carl::Relation cRel = constraint.relation();
            const Poly& lhs = constraint.lhs();

            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational rhs = lhs.constantPart(); // TODO extract constant or check whether we actually need it.
            Rational sum  = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;

            // TODO check whether there is a better way to get the number of terms in a poly
            const std::size_t lhsSize = lhs.size() - lhs.hasConstantTerm() ? 1 : 0;

            // check each monome for negative/positive coefficient
            for(const auto& it : lhs){
                // TODO make sure we do not take a constant part into account
                if(it.coeff() < 0){
                    positive = false;
                }else if(it.coeff() > 0){
                    negative = false;
                }

                if(it.coeff() < min){
                    min = it.coeff();
                }else if(it.coeff() > max){
                    max = it.coeff();
                }

                sum += it.coeff();
            }

            for(unsigned i = 0; i < lhsSize - 1; i++){
                // check whether the coefficients are all the same
                if(lhs[i].coeff() != lhs[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = encodeMixedConstraints(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (lhs.lcoeff() == 1 || lhs.lcoeff() == -1 ) && lhsSize > 1){
                // x1 + x2 - x3 ~ b
                auto res = encodeCardinalityConstraint(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else if((lhsSize == 1 && !lhs.begin()->isConstant()) || lhsSize == 2){
                // TODO only one term, probably this case will never be reached.
                auto res = convertSmallFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else if(!(positive && rhs > 0 && sum > rhs
                        && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
                    &&  !(negative && rhs < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < rhs)
                    && !(negative && rhs < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < rhs)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum != rhs && rhs != 0)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum == rhs && rhs != 0)
                    && !(!positive && !negative)
                    ){
                auto res = convertBigFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeWithRNS(const FormulaT& formula){
            assert(formula.getType() == carl::FormulaType::CONSTRAINT);

            const ConstraintT& constraint = formula.constraint();
            carl::Relation cRel  = constraint.relation();
            const auto& cLHS = constraint.lhs();
            bool positive = true;
            Rational sum  = 0;
            bool isAllCoeffEqual = true;

            for(auto it = cLHS.begin(); it != cLHS.end(); ++it){
                sum += it->coeff();
                if(it->coeff() < 0){
                    positive = false;
                }
            }

            for(unsigned i = 0; i < cLHS.size() - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            // TODO we want to further distinguish whether we need 4 or 5 since we might have a constant term
            if(positive && !(isAllCoeffEqual && cLHS.lcoeff() == 1) && cRel == carl::Relation::EQ && cLHS.size() > 4){
                initPrimesTable();
                std::vector<Integer> base = calculateRNSBase(constraint);
                if(base.size() != 0 && isNonRedundant(base, constraint)){
                    std::vector<FormulaT> subformulas;
                    for(auto i : base){
                        subformulas.push_back(rnsTransformation(constraint, i));
                    }
                    auto res = FormulaT(carl::FormulaType::AND, std::move(subformulas));
                    SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                    return res;
                }else{
                    return checkFormulaType(formula);
                }
            }else{
                return checkFormulaType(formula);
            }
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeWithCardConstr(const FormulaT& formula){
            assert(formula.getType() == carl::FormulaType::CONSTRAINT);

            const ConstraintT& constraint = formula.constraint();
            carl::Relation cRel = constraint.relation();
            const auto& cLHS = constraint.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = constraint.constantPart();
            Rational sum  = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;

            // TODO substract 1 if there is a constant term
            std::size_t lhsSize = cLHS.size();

            for(auto it : cLHS){
                if(it.coeff() < 0){
                    positive = false;
                }else if(it.coeff() > 0){
                    negative = false;
                }

                if(it.coeff() < min){
                    min = it.coeff();
                }else if(it.coeff() > max){
                    max = it.coeff();
                }
                sum += it.coeff();
            }

            for(unsigned i = 0; i < lhsSize - 1; i++){
                // TODO this might blow up if we check the constant term
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = encodeCardinalityConstraint(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(!(positive && cRHS > 0 && sum > cRHS
                        && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
                    &&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS)
                    && !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
                    && !(!positive && !negative)
                    ){
                auto res = convertBigFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeWithMixedConstr(const FormulaT& formula){
            // preprocess this legacy type first
            assert(formula.getType() == carl::FormulaType::CONSTRAINT);

            const ConstraintT& constraint = formula.constraint();
            carl::Relation cRel = constraint.relation();
            const Poly& cLHS = constraint.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = constraint.constantPart();
            Rational sum  = 0;

            // TODO substract 1 if we have a constant term
            std::size_t lhsSize = cLHS.size();

            for(auto it : cLHS){
                if(it.coeff() < 0){
                    positive = false;
                }else if(it.coeff() > 0){
                    negative = false;
                }

                sum += it.coeff();
            }

            for(unsigned i = 0; i < lhsSize - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = encodeMixedConstraints(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(!(positive && cRHS > 0 && sum > cRHS
                        && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
                    &&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS)
                    && !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
                    && !(!positive && !negative)
                    ){
                auto res = convertBigFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeBasic(const FormulaT& formula){
            assert(formula.getType() == carl::FormulaType::CONSTRAINT);

            const ConstraintT& constraint = formula.constraint();
            carl::Relation cRel = constraint.relation();
            const auto& cLHS = constraint.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = constraint.constantPart();
            Rational sum  = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;
            // TODO substract 1 if we have a constant part
            std::size_t lhsSize = cLHS.size();

            for(auto it : cLHS){
                if(it.coeff() < 0){
                    positive = false;
                }else if(it.coeff() > 0){
                    negative = false;
                }

                if(it.coeff() < min){
                    min = it.coeff();
                }else if(it.coeff() > max){
                    max = it.coeff();
                }
                sum += it.coeff();
            }

            for(unsigned i = 0; i < lhsSize - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(!(positive && cRHS > 0 && sum > cRHS
                        && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
                    &&  !(negative && cRHS < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < cRHS)
                    && !(negative && cRHS < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < cRHS)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum != cRHS && cRHS != 0)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum == cRHS && cRHS != 0)
                    && !(!positive && !negative)
                    ){
                auto res = convertBigFormula(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::encodeMixedConstraints(const ConstraintT& formula){
            const ConstraintT& c = formula;
            carl::Relation cRel = formula.relation();
            const Poly& cLHS = formula.lhs();
            auto cVars = formula.variables();
            Rational cRHS = formula.constantPart();
            Rational sum  = 0;
            Rational sumNegCoef = 0;
            Rational sumPosCoef = 0;
            Rational numberNegCoef = 0;
            Rational numberPosCoef = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;
            std::size_t lhsSize = cLHS.size();

            for(const auto& it : cLHS){
                if(it.coeff() < 0){
                    sumNegCoef -= it.coeff();
                    numberNegCoef++;
                }else if(it.coeff() > 0){
                    sumPosCoef += it.coeff();
                    numberNegCoef++;
                }

                if(it.coeff() < min){
                    min = it.coeff();
                }else if(it.coeff() > max){
                    max = it.coeff();
                }
                sum += it.coeff();
            }

            if(cRel == carl::Relation::GEQ){
                if(lhsSize == 2){
                    if(cRHS == max && sum == 0){
                        //-1 x1 +1 x2 >= 1 ===> not x1 and x2
                        FormulasT subf;
                        for(const auto& it : cLHS){
                            if(it.coeff() < 0){
                                FormulaT variableFormula = FormulaT(it.getSingleVariable());
                                subf.push_back(FormulaT(carl::FormulaType::NOT, variableFormula));
                            }else{
                                subf.push_back(FormulaT(it.getSingleVariable()));
                            }
                        }
                        return FormulaT(carl::FormulaType::AND, std::move(subf));
                    }else if(cRHS == 0 && sum == 0){
                        //+1 x1 -1 x2 >= 0 ==> x2 -> x1 ===> not x2 or x1
                        FormulasT subf;
                        for(const auto& it : cLHS){
                            if(it.coeff() < 0){
                                FormulaT variableFormula = FormulaT(it.getSingleVariable());
                                subf.push_back(FormulaT(carl::FormulaType::NOT, variableFormula));
                            }else{
                                subf.push_back(FormulaT(it.getSingleVariable()));
                            }
                        }
                        return FormulaT(carl::FormulaType::OR, std::move(subf));
                    }else if(cRHS == min && sum == 0){
                        //-1 x1 + 1 x2 >= -1 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else if(lhsSize == 3){
                    if(numberNegCoef == 2 && (sumNegCoef/numberNegCoef) == 1 && sum == min &&  min == - max){
                        if(cRHS == 0){
                            //-1 x1 -1 x2 +1 x3 >= 0 ===> not(x1 and x2) and ((x1 or x2) -> x3)
                            std::set<carl::Variable> nVars;
                            carl::Variable pVar;
                            for(const auto& it : cLHS){
                                if(it.coeff() < 0){
                                    nVars.insert(it.getSingleVariable());
                                }else{
                                    pVar = it.getSingleVariable();
                                }
                            }
                            FormulaT subfA = FormulaT(carl::FormulaType::NOT, generateVarChain(nVars, carl::FormulaType::AND));
                            FormulaT subfB = FormulaT(carl::FormulaType::IMPLIES, generateVarChain(nVars, carl::FormulaType::OR), FormulaT(pVar));
                            return FormulaT(carl::FormulaType::AND, subfA, subfB);
                        }else if(cRHS == max){
                            //-1 x1 -1 x2 +1 x3 >= 1 ===> x3
                            carl::Variable posVar;
                            for(auto it : cLHS){
                                if(it.coeff() > 0){
                                    posVar = it.getSingleVariable();
                                    break;
                                }
                            }
                            return FormulaT(posVar);
                        }else if(cRHS == min){
                            //-1 x1 -1 x2 +1 x3 >= -1 ===> (x1 and x2) -> x3 ===> not x1 or not x2 or x3
                            FormulasT subformulas;
                            for(const auto& it : cLHS){
                                if(it.coeff() < 0){
                                    subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.getSingleVariable())));
                                }else{
                                    subformulas.push_back(FormulaT(it.getSingleVariable()));
                                }
                            }
                            return FormulaT(carl::FormulaType::OR, std::move(subformulas));
                        }else{
                            return forwardAsArithmetic(c);
                        }
                    }else if(numberPosCoef == 2 && (sumPosCoef/numberPosCoef) == 1 && sum == max && min == - max){
                        if(cRHS == 0){
                            //-1 x1 +1 x2 +1 x3 >= 0 ===> x1 -> (x2 or x3) ===> not x1 or x2 or x3
                            FormulasT subformulas;
                            for(const auto& it : cLHS){
                                if(it.coeff() < 0){
                                    subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it.getSingleVariable())));
                                }else{
                                    subformulas.push_back(FormulaT(it.getSingleVariable()));
                                }
                            }
                            return FormulaT(carl::FormulaType::OR, std::move(subformulas));
                        }else if(cRHS == min){
                            //-1 x1 +1 x2 +1 x3 >= -1 ===> true
                            return FormulaT(carl::FormulaType::TRUE);
                        }else if(cRHS == max){
                            //-1 x1 +1 x2 +1 x3 >= 1 ===> x1 -> (x2 and x3) and (x1 or x2 or x3)
                            FormulaT subfA = generateVarChain(cVars, carl::FormulaType::OR);
                            carl::Variable nVar;
                            std::set<carl::Variable> pVars;
                            for(const auto& it : cLHS){
                                if(it.coeff() > 0){
                                    pVars.insert(it.getSingleVariable());
                                }else{
                                    nVar = it.getSingleVariable();
                                }
                            }
                            FormulaT subfB = FormulaT(carl::FormulaType::IMPLIES, FormulaT(nVar), generateVarChain(pVars, carl::FormulaType::AND));
                            return FormulaT(carl::FormulaType::AND, subfA, subfB);
                        }else{
                            return forwardAsArithmetic(c);
                        }
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else if(numberPosCoef == lhsSize - 1 && (sumPosCoef / numberPosCoef) == 1 && cRHS == 0 && sum == lhsSize - 1){
                    //+1 x513 +1 x417 -1 x257 +1 x65 +1 x1 >= 0  ===> +1 x513 +1 x417 +1 x65 +1 x1 >= 1 or +1 x513 +1 x417 +1 x65 +1 x1 >= 0
                    Poly newLHS;
                    for(const auto& it : cLHS){
                        if(it.coeff() > 0){
                            newLHS += it;
                        }
                    }

                    // actually newLHS - 1 in the next line
                    ConstraintT constrA(newLHS + Poly(-1), carl::Relation::GEQ);
                    ConstraintT constrB(newLHS, carl::Relation::GEQ);
                    FormulaT f = FormulaT(carl::FormulaType::OR, FormulaT(constrA), FormulaT(constrB));
                    ConstraintT PBf = f.constraint();
                    return convertBigFormula(PBf);
                }else{
                    return forwardAsArithmetic(c);
                }
            }else{
                return forwardAsArithmetic(c);
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::encodeCardinalityConstraint(const ConstraintT& formula){
            const ConstraintT& c = formula;
            const auto& cLHS = formula.lhs();
            auto cVars = formula.variables();
            Rational cRHS = formula.constantPart();
            carl::Relation cRel = formula.relation();
            // TODO lhsSize probably not correct
            std::size_t lhsSize = cLHS.size();
            Rational firstCoef = cLHS[0].coeff();
            Rational sum = 0;

            // since the constraint is normalized, we should never have GEQ or GREATER
            assert(cRel != carl::Relation::GEQ && cRel != carl::Relation::GREATER);

            for(const auto& it : cLHS){
                sum += it.coeff();
            }

            if(cRel == carl::Relation::GEQ){
                if(firstCoef == -1 && cRHS == 1){
                    //-1 x1 -1 x2 -1 x3 -1 x4 >= 1
                    return FormulaT(carl::FormulaType::FALSE);
                }else if(firstCoef == 1 && cRHS > sum){
                    //x1 + x2 + x3 + x4 >= 5
                    return FormulaT(carl::FormulaType::FALSE);
                }else if(firstCoef == 1 && cRHS == 1){
                    //+1 x1 +1 x2 +1 x3 >= 1 ===> x1 or x2 or x3
                    FormulasT subformulas;
                    for(auto it : cVars){
                        subformulas.push_back(FormulaT(it));
                    }
                    return FormulaT(carl::FormulaType::OR, std::move(subformulas));
                }else if(firstCoef == -1 && cRHS == -1){
                    //-1 x1 -1 x2 -1 x3 -1 x4 >= -1 ===> (x1 and not x2 and not x3 and not x4) or (notx1 andx2 and not x3 and not x4) or ...
                    //or (not x1 and not x2 and not x3 and not x4)

                    // TODO rename me
                    FormulasT subformulasA;
                    for(unsigned i = 0; i < lhsSize; i++){
                        FormulasT temp;
                        temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
                        for(unsigned j = 0; j < lhsSize; j++){
                            if(i != j){
                                temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[j].getSingleVariable())));
                            }
                        }
                        subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
                    }
                    FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

                    FormulasT subformulasB;
                    for(const auto& it : cVars){
                        subformulasB.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
                    }
                    FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

                    return FormulaT(carl::FormulaType::OR, subformulaA, subformulaB);
                }else if(firstCoef == -1 && cRHS < 0 && cRHS > sum){
                    //-1 x1 -1 x2 -1 x3 -1 x4 >= -2 ===>
                    FormulasT subsubformulas;
                    for(int j = 0; j < (cRHS* -1); j++){
                        std::vector<int> signs;
                        for(std::size_t i = 0; i < lhsSize - (cRHS* -1) + j; i++){
                            signs.push_back(-1);
                        }
                        for(int i = 0; i < (cRHS* -1) - j; i++){
                            signs.push_back(1);
                        }
                        FormulasT subformulas;
                        do{
                            FormulasT temp;
                            for(unsigned i = 0; i < lhsSize; i++){
                                if(signs[i] == -1){
                                    temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
                                }else{
                                    temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
                                }
                            }
                            subformulas.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
                        }while(std::next_permutation(signs.begin(), signs.end()));
                        subsubformulas.push_back(FormulaT(carl::FormulaType::OR, std::move(subformulas)));
                    }
                    FormulasT subf;
                    for(const auto& it : cVars){
                        subf.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
                    }

                    subsubformulas.push_back(FormulaT(carl::FormulaType::AND, std::move(subf)));
                    return FormulaT(carl::FormulaType::OR, std::move(subsubformulas));
                }else{
                    return forwardAsArithmetic(c);
                }
            }else if(cRel == carl::Relation::EQ){
                if((cRHS > lhsSize && firstCoef == 1) || (firstCoef == 1 && cRHS < 0)){
                    //x1 + x2 + x3 + x4 = 5 or x1 + x2 + x3 + x4 = -2
                    return FormulaT(carl::FormulaType::FALSE);
                }else if((cRHS < lhsSize && firstCoef == -1) || (cRHS > 0 && firstCoef == -1)){
                    //-x1 - x2 - x3 - x4 = -5 || -x1 - x2 - x3 - x4 = 5
                    return FormulaT(carl::FormulaType::FALSE);
                }else if(firstCoef == 1 && cRHS == 0){
                    //+1 x1 +1 x2 +1 x3 +1 x4 = 0  ===> not x1 and not x2 and not x3 and not x4
                    FormulasT subformulas;
                    for(const auto& it : cVars){
                        subformulas.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(it)));
                    }
                    return FormulaT(carl::FormulaType::AND, std::move(subformulas));
                }else if(firstCoef == 1 && cRHS >= 1){
                    // TODO what is happening here?
                    //Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS
                    std::vector<int> sign;
                    for(int i = 0; i < lhsSize - cRHS; i++){
                        sign.push_back(-1);
                    }
                    for(int i = 0; i < cRHS; i++){
                        sign.push_back(1);
                    }
                    FormulasT subformulasA;
                    do{
                        FormulasT temp;
                        for(unsigned i = 0; i < sign.size(); i++){
                            if(sign[i] == 1){
                                temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
                            }else{
                                temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
                            }
                        }
                        subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
                    }while(std::next_permutation(sign.begin(), sign.end()));
                    FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

                    FormulasT subformulasB;
                    for(int j = 1; j < cRHS; j++){
                        //Calculate the signs = [-1, -1, -1, 1, 1] number of 1 is equal cRHS -j
                        std::vector<int> signs;
                        for(int i = 0; i < lhsSize - cRHS + j; i++){
                            signs.push_back(-1);
                        }
                        for(int i = 0; i < cRHS - j; i++){
                            signs.push_back(1);
                        }
                        FormulasT subformulasC;
                        do{
                            FormulasT temp;
                            for(unsigned i = 0; i < signs.size(); i++){
                                if(signs[i] == 1){
                                    temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
                                }else{
                                    temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[i].getSingleVariable())));
                                }
                            }
                            subformulasC.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
                        }while(std::next_permutation(signs.begin(), signs.end()));
                        FormulaT subformulaC = FormulaT(carl::FormulaType::OR, std::move(subformulasC));
                        subformulasB.push_back(FormulaT(carl::FormulaType::NOT, subformulaC));
                    }
                    FormulaT subformulaB = FormulaT(carl::FormulaType::AND, std::move(subformulasB));

                    return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
                }else{
                    //+1 x1 +1 x2 +1 x3 +1 x4 = 3 ===> +1 x1 +1 x2 +1 x3 +1 x4 >= 3 and +1 x1 +1 x2 +1 x3 +1 x4 <= 3
                    ConstraintT newConstA(cLHS - cRHS, carl::Relation::GEQ);
                    ConstraintT newConstB(cLHS - cRHS, carl::Relation::LEQ);

                    FormulaT subformulaA = checkFormulaType(FormulaT(newConstA));
                    FormulaT subformulaB = checkFormulaType(FormulaT(newConstB));
                    return FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);
                }
            }else{
                return forwardAsArithmetic(c);
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::rnsTransformation(const ConstraintT& formula, const Integer& prime) {
            const auto& cLHS = formula.lhs();
            assert(carl::isInteger(formula.constantPart()));
            Integer cRHS = carl::getNum(formula.constantPart());
            Poly newLHS;
            Rational newRHS = carl::mod(cRHS, prime);


            for(const auto& it : cLHS){
                // TODO actually, we only modify the coefficient. Is it enough to modify the coefficient?
                assert(carl::isInteger(it.coeff()));
                Integer newCoeff = carl::mod(carl::getNum(it.coeff()), prime);
                if(newCoeff != 0){
                    newLHS += TermT(newCoeff, it.getSingleVariable(), 1);
                }
            }

            if(newLHS.size() == 0 && newRHS > 0){
                return FormulaT(carl::FormulaType::FALSE);
            }else if(newLHS.size() == 0 && newRHS == 0){
                return FormulaT(carl::FormulaType::TRUE);
            }

            Rational t = 0;
            for(const auto& it : newLHS){
                t += it.coeff();
            }
            t = carl::floor((t - newRHS) / prime );

            for(int i = 0; i < t; i++){
                // newLHS.push_back(std::pair<Rational, carl::Variable>(-t, carl::freshVariable(carl::VariableType::VT_BOOL)));
                newLHS += TermT(-t, carl::freshBooleanVariable(), 1);
            }

            ConstraintT newConstraint(newLHS - newRHS, carl::Relation::EQ);
            return checkFormulaType(FormulaT(newConstraint));
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::convertSmallFormula(const ConstraintT& formula){
            SMTRAT_LOG_DEBUG("smtrat.pbc", "Trying to convert small formula: " << formula);
            assert(!formula.lhs().begin()->isConstant());

            const ConstraintT& c = formula;
            carl::Relation cRel = formula.relation();
            const auto& cLHS = formula.lhs();
            Rational lhsCoeff = cLHS.begin()->coeff();
            FormulaT lhsVar = FormulaT(cLHS.begin()->getSingleVariable());
            Rational cRHS = formula.constantPart();

            if(cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER){
                if(lhsCoeff > 0){
                    if(cRHS < lhsCoeff && cRHS < 0){
                        //5 x1 >= -3 or 5 x1 > -3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS < lhsCoeff && cRHS > 0){
                        //5 x1 >= 3 or 5 x1 > 3 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS == 0 && cRel == carl::Relation::GEQ){
                        //5 x1 >= 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == 0 && cRel == carl::Relation::GREATER){
                        //5 x1 > 0 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS > lhsCoeff){
                        //10 x1 >= 12 or 10 x1 > 12 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::GEQ){
                        //10 x1 >= 10 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::GREATER){
                        //10 x1 > 10 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else if(lhsCoeff < 0){
                    if(cRHS < lhsCoeff){
                        //-10 x1 >= -20 or -10 x1 > -20 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == 0 && cRel == carl::Relation::GEQ){
                        //-2 x1 >= 0 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else if(cRHS == 0 && cRel == carl::Relation::GREATER){
                        //-3 x1 > 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS > 0){
                        //-2 x1 >= 10 or -2 x1 > 10 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS > lhsCoeff && cRHS < 0){
                        //-20 x1 >= -3 or -20 x1 > -3 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else if(cRHS > lhsCoeff && cRHS > 0){
                        //-20 x1 >= 3 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::GEQ){
                        //-20 x1 >= -20 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::GREATER){
                        //-20 x1 > -20 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else{ //lhsCoeff == 0
                    if(cRHS > 0){
                        // 0 x2 > 3 or 0 x2 >= 3 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS == 0 && cRel == carl::Relation::GEQ){
                        //0 x2 >= 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == 0 && cRel == carl::Relation::GREATER){
                        //0 x2 > 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS < 0){
                        // 0 x2 > -3 or 0 x2 >= -3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }
            }else if(cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS){
                if(lhsCoeff > 0){
                    if(cRHS < lhsCoeff && cRHS > 0){
                        //10 x1 <= 3 or 10 x1 < 3 ===>  not x1
                        return FormulaT(lhsVar.negated());
                    }else if(cRHS < lhsCoeff && cRHS < 0){
                        //10 x1 <= -2 or 10 x1 < -2 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS == 0 && cRel == carl::Relation::LEQ){
                        //10 x1 <= 0 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else if(cRHS == 0 && cRel == carl::Relation::LESS){
                        //10 x1 < 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS > lhsCoeff){
                        //6 x1 <= 39 or 3 x1 < 23 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::LEQ){
                        //3 x1 <= 3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::LESS){
                        //3 x1 < 3 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else if(lhsCoeff < 0){
                    if(cRHS < lhsCoeff){
                        //-3 x1 <= -43 or -3 x1 < -43 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS == 0 && cRel == carl::Relation::LEQ){
                        //-3 x1 <= 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == 0 && cRel == carl::Relation::LESS){
                        //-3 x1 < 0 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS > 0){
                        //-3 x1 <= 5 or -3 x1 < 5 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS > lhsCoeff && cRHS < 0){
                        //-30 x1 <= -5 or -30 x1 < -5 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS > lhsCoeff && cRHS > 0){
                        //-30 x1 <= 5 or -30 x1 < 5 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::LEQ){
                        //-20 x1 <= -20 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS == lhsCoeff && cRel == carl::Relation::LESS){
                        //-20 x1 < -20 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else{ //lhsCoeff == 0
                    if(cRHS == 0 && cRel == carl::Relation::LEQ){
                        //0 x2 <= 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS == 0 && cRel == carl::Relation::LESS){
                        //0 x3 < 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS < 0){
                        //0 x2 < -3 or 0 x2 <= -3 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS > 0){
                        //0 x2 < 3 or 0 x3 <= 3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }
            }else if(cRel == carl::Relation::EQ){
                if(lhsCoeff != 0){
                    if(lhsCoeff == cRHS){
                        //-2 x1 = -2 or 3 x1 = 3 ===> x1
                        return FormulaT(lhsVar);
                    }else if(cRHS == 0){
                        //2 x1 = 0 or -3 x1 = 0 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else{
                        //2 x1 = 4 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }
                }else{
                    if(cRHS == 0){
                        // 0 x2 = 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(cRHS != 0){
                        // 0 x3 = 3 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }
            }else if(cRel == carl::Relation::NEQ){
                if(lhsCoeff != 0){
                    if(lhsCoeff == cRHS){
                        //3 x1 != 3 ===> not x1
                        return FormulaT(lhsVar.negated());
                    }else if(cRHS == 0){
                        //3 x1 != 0 ===> x1
                        return FormulaT(lhsVar);
                    }else if(lhsCoeff != cRHS){
                        //3 x1 != 5 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }else{
                    if(cRHS == 0){
                        // 0 x2 != 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(cRHS != 0){
                        // 0 x3 != 3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{
                        return forwardAsArithmetic(c);
                    }
                }
            }
            return FormulaT(formula);
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::convertBigFormula(const ConstraintT& formula){
            const ConstraintT& c = formula;
            const auto& cLHS = formula.lhs();
            carl::Relation cRel = formula.relation();
            std::set<carl::Variable> cVars = formula.variables();
            Rational cRHS = formula.constantPart();
            bool positive = true;
            bool negative = true;
            Rational sum = 0;

            for(auto it : cLHS){
                if(it.coeff() < 0){
                    positive = false;
                }else if(it.coeff() > 0){
                    negative = false;
                }
                sum += it.coeff();
            }

            if(positive && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
                if(cRHS < 0){
                    //5 x1 + 2 x2 + 3 x3 >= -5 or 5 x1 + 2 x2 + 3 x3 > -5
                    //===> false -> x1 AND x2 AND x3 ===> TRUE
                    return FormulaT(carl::FormulaType::TRUE);
                }else if(cRHS == 0){
                    if(cRel == carl::Relation::GEQ){
                        // 5 x1 + 2 x2 + 3 x3 >= 0 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }
                    // 5 x1 + 2 x2 + 3 x3 > 0 ===> x1 or x2 or x3
                    return generateVarChain(cVars, carl::FormulaType::OR);
                }else{//RHS > 0
                    if(sum < cRHS){
                        //5 x1 + 2 x2 + 3 x3 >= 20 or 5 x1 + 2 x2 + 3 x3 > 20 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(sum == cRHS && cRel == carl::Relation::GEQ){
                        //5 x1 + 2 x2 + 3 x3 >= 10 ===> x1 and x2 and x3
                        return generateVarChain(cVars, carl::FormulaType::AND);
                    }else if(sum == cRHS && cRel == carl::Relation::GREATER){
                        //5 x1 + 2 x2 + 3 x3 > 10 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }//sum > cRHS
                }
            }else if(negative && (cRel == carl::Relation::GREATER || cRel == carl::Relation::GEQ)){
                if(cRHS > 0){
                    //-5 x1 - 2 x2 - 3 x3 >= 5 or -5 x1 - 2 x2 - 3 x3 > 5 ===> FALSE
                    return FormulaT(carl::FormulaType::FALSE);
                }else if(cRHS == 0){
                    if(cRel == carl::Relation::GEQ){
                        //-5 x1 - 2 x2 - 3 x3 >= 0 ===> (x1 or x2 or x3) -> false
                        FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
                        FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }else{ // cRel == carl::Relation::GREATER
                        //-5 x1 - 2 x2 - 3 x3 > 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }
                }else{ //cRHS < 0
                    if(sum == cRHS && cRel == carl::Relation::GEQ){
                        //-5 x1 - 2 x2 - 3 x3 >= -10  ===> false -> x1 and x2 and x3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(sum == cRHS && cRel == carl::Relation::GREATER){
                        //-5 x1 - 2 x2 - 3 x3 > -10  ===> x1 and x2 and x3 -> false
                        FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
                        FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }else if(sum > cRHS){
                        //-3 x1 -3 x2 -1 x3 >= -20 or -3 x1 -3 x2 -1 x3 > -20 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }//sum < cRHS
                }
            }else if(positive && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
                if(cRHS < 0){
                    //5 x1 +2 x2 +3 x3 <= -5 or 5 x1 +2 x2 +3 x3 < -5 ===> FALSE
                    return FormulaT(carl::FormulaType::FALSE);
                }else if(cRHS == 0){
                    if(cRel == carl::Relation::LEQ){
                        //5 x1 +2 x2 +3 x3 <= 0 ===> (x1 or x2 or x3) -> false
                        FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
                        FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }else{ //cRel == carl::Relation::LESS
                        //5 x1 +2 x2 +3 x3 < 0 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }
                }else{ //cRHS > 0
                    if(sum == cRHS && cRel == carl::Relation::LEQ){
                        //5 x1 +2 x2 +3 x3 <= 10 ===> false -> x1 and x2 and x3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else if(sum == cRHS && cRel == carl::Relation::LESS){
                        //5 x1 +2 x2 +3 x3 < 10 ===> x1 and x2 and x3 -> false
                        FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
                        FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }else if(sum < cRHS){
                        //5 x1 +2 x2 +3 x3 <= 20 or 5 x1 +2 x2 +3 x3 < 20 ===> false -> x1 and x2 and x3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }//sum > cRHS
                }
            }else if(negative && (cRel == carl::Relation::LESS || cRel == carl::Relation::LEQ)){
                if(cRHS > 0){
                    //-5 x1 -2 x2 -3 x3 <= 5 or -5 x1 -2 x2 -3 x3 < 5 ===> false -> x1 and x2 and x3 ===> TRUE
                    return FormulaT(carl::FormulaType::TRUE);
                }else if(cRHS == 0){
                    if(cRel == carl::Relation::LEQ){
                        //-5 x1 -2 x2 -3 x3 <= 0 ===> false -> x1 and x2 and x3 ===> TRUE
                        return FormulaT(carl::FormulaType::TRUE);
                    }else{ //cRel == carl::Relation::LESS
                        //-5 x1 -2 x2 -3 x3 < 0 ===> true -> x1 or x2 or x3
                        FormulaT subformulaA = FormulaT(carl::FormulaType::TRUE);
                        FormulaT subformulaB = generateVarChain(cVars, carl::FormulaType::OR);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }
                }else{ //cRHS < 0
                    if(sum > cRHS){
                        //-5 x1 -2 x2 -3 x3 < -15 or -5 x1 -2 x2 -3 x3 <= -15 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }else if(sum == cRHS && cRel == carl::Relation::LEQ){
                        //-5 x1 -2 x2 -3 x3 <= -10 ===> x1 and x2 and x3 -> false
                        FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
                        FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                        return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                    }else if(sum == cRHS && cRel == carl::Relation::LESS){
                        //-5 x1 -2 x2 -3 x3 < -10 ===> FALSE
                        return FormulaT(carl::FormulaType::FALSE);
                    }// sum < cRHS
                }
            }else if(cRel == carl::Relation::EQ){
                if(sum == cRHS){
                    //5 x1 +2 x2 +3 x3 = 10 ===> x1 and x2 and x3
                    return generateVarChain(cVars, carl::FormulaType::AND);
                }else if(sum != cRHS && cRHS == 0){
                    //5 x1 +2 x2 +3 x3 = 0 ===> (x1 or x2 or x3 -> false)
                    FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::OR);
                    FormulaT subformulaB = FormulaT(carl::FormulaType::FALSE);
                    return FormulaT(carl::FormulaType::IMPLIES, subformulaA, subformulaB);
                }else{
                    return forwardAsArithmetic(c);
                }
            }else if(cRel == carl::Relation::NEQ){
                if(sum != cRHS && cRHS == 0){
                    //5 x1 +2 x2 +3 x3 = 0 ===> not(x1 and x2 and x3)
                    FormulaT subformulaA = generateVarChain(cVars, carl::FormulaType::AND);
                    return FormulaT(carl::FormulaType::NOT, subformulaA);
                }else{
                    return forwardAsArithmetic(c);
                }
            }
            return FormulaT(formula);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::generateVarChain(const std::set<carl::Variable>& vars, carl::FormulaType type){
            FormulasT newSubformulas;
            for(const auto& var: vars){
                FormulaT newFormula = FormulaT(var);
                newSubformulas.push_back(newFormula);
            }
            return FormulaT(type, std::move(newSubformulas));
        }


    /*
       / Converts Constraint into a LRA formula.
       */
    template<typename Settings>
        FormulaT PBPPModule<Settings>::forwardAsArithmetic(const ConstraintT& formula){
            const auto& cLHS = formula.lhs();
            carl::Relation cRel  = formula.relation();
            Rational cRHS = formula.constantPart();
            auto variables = formula.variables();

            for(const auto& it : variables){
                mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(it, carl::freshBooleanVariable()));
            }

            Poly lhs;
            for(const auto& it : cLHS){
                // Poly pol(it.second);
                if (!it.isConstant()) {
                  lhs = lhs + it.coeff() * it.getSingleVariable();
                } else {
                    lhs = lhs + it.coeff();
                }
            }

            FormulaT subformulaA = FormulaT(lhs, cRel);

            // Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
            // FormulaT subformulaB = createAuxiliaryConstraint(variables);
            // FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

            //Adding auxiliary constraint to interconnect the bool and int variables
            FormulaT subformulaD = interconnectVariables(variables);
            return FormulaT(carl::FormulaType::AND, subformulaA, subformulaD);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::interconnectVariables(const std::set<carl::Variable>& variables){
            FormulasT subformulas;
            for(const auto& var : variables){
                if(std::find(mConnectedVars.begin(), mConnectedVars.end(), var) == mConnectedVars.end()){
                    //The variables are not interconnected
                    mConnectedVars.push_back(var);
                    FormulaT boolVar = FormulaT(mVariablesCache.find(var)->second);
                    Poly intVar(var);
                    FormulaT subformulaA = FormulaT(intVar - Rational(1), carl::Relation::EQ);
                    FormulaT subformulaB = FormulaT(carl::FormulaType::IMPLIES, boolVar, subformulaA);
                    FormulaT subformulaC = FormulaT(intVar, carl::Relation::EQ);
                    FormulaT subformulaD = FormulaT(carl::FormulaType::IMPLIES, boolVar.negated(), subformulaC);
                    FormulaT newFormula  = FormulaT(carl::FormulaType::AND, subformulaB, subformulaD);
                    subformulas.push_back(newFormula);

                }
            }
            return FormulaT(carl::FormulaType::AND, std::move(subformulas));
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::createAuxiliaryConstraint(const std::vector<carl::Variable>& variables){
            FormulasT subformulas;
            for(auto it : variables){
                if(std::find(mCheckedVars.begin(), mCheckedVars.end(), it) == mCheckedVars.end()){
                    //There are no auxiliary constraints for this variable
                    mCheckedVars.push_back(it);
                    Poly intVar(it);
                    FormulaT subformulaA = FormulaT(intVar, carl::Relation::EQ);
                    FormulaT subformulaB = FormulaT(intVar - Rational(1), carl::Relation::EQ);
                    FormulaT newFormula = FormulaT(carl::FormulaType::XOR, subformulaA, subformulaB);
                    subformulas.push_back(newFormula);
                }
            }
            return FormulaT(carl::FormulaType::AND, std::move(subformulas));
        }




    template<typename Settings>
        std::vector<Integer> PBPPModule<Settings>::calculateRNSBase(const ConstraintT& formula){
            const auto& cLHS = formula.lhs();
            std::vector<std::pair<int, Integer>> freq;
            Rational sum = 0;
            Rational product = 1;
            std::vector<Integer> base;

            for(auto it : cLHS){
                assert(carl::isInteger(it.coeff()));
                sum += carl::getNum(it.coeff());
            }

            for(auto it : cLHS){
                assert(carl::isInteger(it.coeff()));
                std::vector<Integer> v = integerFactorization(carl::getNum(it.coeff()));
                std::sort(v.begin(), v.end());
                v.erase( unique( v.begin(), v.end() ), v.end() );

                for(auto i : v){
                    auto elem = std::find_if(freq.begin(), freq.end(),
                            [&] (const pair<int, Integer>& elem){
                            return elem.second == i;
                            });
                    if(elem != freq.end()){
                        auto distance = std::distance(freq.begin(), elem);
                        freq[(unsigned long) distance].first = freq[(unsigned long) distance].first + 1;
                    }else{
                        freq.push_back(std::pair<int, Integer>(1, i));
                    }
                }
            }

            std::sort(freq.begin(), freq.end(),
                    [&](const pair<int, Integer> &p1, const pair<int, Integer> &p2)
                    {
                    if(p1.first == p2.first){
                    return (p1.second < p2.second);
                    }else{
                    return(p1.first > p2.first);
                    }
                    });


            for(auto it : freq){
                if(it.second != 0){
                    product *= it.second;
                    if(product <= sum){
                        base.push_back(it.second);
                    }else{
                        base.push_back(it.second);
                        break;
                    }
                }

            }

            for(std::size_t i = 0; i < base.size(); i++){
                if(base[i] == 1 || base[i] == 0){
                    base.erase(base.begin() +  (long) i);
                }
            }
            return base;
        }


    template<typename Settings>
        std::vector<Integer>PBPPModule<Settings>::integerFactorization(const Integer& coeff){
            if(coeff <= 100){
                return mPrimesTable[carl::toInt<std::size_t>(coeff)];
            }

            std::vector<Integer> primes;
            Integer x = carl::ceil(carl::sqrt(coeff));
            Integer y = (x * x) - coeff;
            Integer r = carl::floor(carl::sqrt(y));

            if(coeff % 2 == 0){
                primes.push_back((carl::uint) 2);
                if(coeff / 2 > 2){
                    std::vector<Integer> v = integerFactorization(coeff / 2);
                    primes.insert(primes.end(), v.begin(), v.end());
                }
            }else{
                while(y >  r * r){
                    x++;
                    y = (x * x) - coeff;
                    r = carl::floor(carl::sqrt(y));
                }

                Integer first = x + r;
                Integer second  = x - r;

                if(first > 1){
                    if(first <= 100){
                        std::vector<Integer> v = mPrimesTable[carl::toInt<std::size_t>(first)];
                        primes.insert(primes.end(), v.begin(), v.end());

                    }else{
                        carl::PrimeFactory<Integer> pFactory;
                        Integer prime = pFactory[24];
                        while(prime < first){
                            prime = pFactory.nextPrime();
                        }
                        if(prime == first){
                            //first is a big prime number
                            primes.push_back(first);
                        }else{
                            //first is not a prime number
                            std::vector<Integer> v = integerFactorization(first);
                            primes.insert(primes.end(), v.begin(), v.end());
                        }
                    }
                }

                if(second > 1){
                    if(second <= 100){
                        std::vector<Integer> v = mPrimesTable[carl::toInt<std::size_t>(second)];
                        primes.insert(primes.end(), v.begin(), v.end());
                    }else{
                        carl::PrimeFactory<Integer> pFactory;
                        Integer prime = pFactory[24];
                        while(prime < second){
                            prime = pFactory.nextPrime();
                        }
                        if(prime == second){
                            //second is a big prime number
                            primes.push_back(second);
                        }else{
                            //second is not a prime number
                            std::vector<Integer> v = integerFactorization(second);
                            primes.insert(primes.end(), v.begin(), v.end());
                        }
                    }
                }
            }
            return primes;
        }
    template<typename Settings>
        bool PBPPModule<Settings>::isAllCoefficientsEqual(const ConstraintT& constraint) {
            Rational coefficient = constraint.lhs().lcoeff();
            for (const auto& term : constraint.lhs()) {
                if (term.coeff() != coefficient) {
                    return false;
                }
            }

            return true;
        }

    template<typename Settings>
        bool PBPPModule<Settings>::isNonRedundant(const std::vector<Integer>& base, const ConstraintT& formula){
            const auto& cLHS = formula.lhs();
            Rational max = INT_MIN;
            Rational sum = 0;
            Rational product = 1;
            carl::PrimeFactory<Integer> pFactory;


            for(auto it : cLHS){
                if(it.coeff() > max){
                    max = it.coeff();
                }
                sum += it.coeff();
            }

            for(auto it : base){
                if(it >= max){
                    return false;
                }
            }

            for(Rational i = 0; i < max; i++){
                product *= pFactory.nextPrime();
            }

            if(sum > product){
                return false;
            }

            return true;
        }


    template<typename Settings>
        void PBPPModule<Settings>::initPrimesTable(){
            //The 0 and 1 MUST be here in order to pick the right factorization!
            mPrimesTable = {{0}, {1}, {2}, {3}, {2, 2}, {5}, {2, 3}, {7}, {2, 2, 2}, {3, 3}, {2, 5}, {11}, {2, 2, 3},
                {13}, {2, 7}, {3, 5}, {2, 2, 2, 2}, {17}, {2, 3, 3}, {19}, {2, 2, 5}, {3, 7}, {2, 11},
                {23}, {2, 2, 2, 3}, {5, 5}, {2, 13}, {3, 3, 3}, {2, 2, 7}, {29}, {2, 3, 5}, {31},
                {2, 2, 2, 2, 2}, {3, 11}, {2, 17}, {5, 7}, {2, 2, 3, 3}, {37}, {2, 19}, {3, 13}, {2, 2, 2, 5},
                {41}, {2, 3, 7}, {43}, {2, 2, 11}, {3, 3, 5}, {2, 23}, {47}, {2, 2, 2, 2, 3}, {7 ,7}, {2, 5, 5},
                {3, 17}, {2, 2, 13}, {53}, {2, 3, 3, 3}, {5, 11}, {2, 2, 2, 7}, {3, 19}, {2, 29}, {59},
                {2, 2, 3, 5}, {61}, {2, 31}, {3, 3, 7}, {2, 2, 2, 2, 2, 2}, {5, 13}, {2, 3, 11}, {67},
                {2, 2, 17}, {3, 23}, {2, 5, 7}, {71}, {2, 2, 2, 3, 3}, {73}, {2, 37}, {3, 5, 5}, {2, 2, 19},
                {7, 11}, {2, 3, 13}, {79}, {2, 2, 2, 2, 5}, {3, 3, 3, 3}, {2, 41}, {83}, {2, 2, 3, 7}, {5, 17},
                {2, 43}, {3, 29}, {2, 2, 2, 11}, {89}, {2, 3, 3, 5}, {7, 13}, {2, 2, 23}, {3, 31}, {2, 47},
                {5, 19}, {2, 2, 2, 2, 2, 3}, {97}, {2, 7, 7}, {3, 3, 11}, {2, 2, 5, 5}};
        }

}

#include "Instantiation.h"
