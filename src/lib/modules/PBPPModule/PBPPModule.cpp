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
                checkFormulaTypeFunction = std::bind(&PBPPModule<Settings>::checkFormulaType, this, std::placeholders::_1);
                checkFormulaTypeWithRNSFunction = std::bind(&PBPPModule<Settings>::checkFormulaTypeWithRNS, this, std::placeholders::_1);
                checkFormulaTypeWithCardConstrFunction = std::bind(&PBPPModule<Settings>::checkFormulaTypeWithCardConstr, this, std::placeholders::_1);
                checkFormulaTypeWithMixedConstrFunction = std::bind(&PBPPModule<Settings>::checkFormulaTypeWithMixedConstr, this, std::placeholders::_1);
                checkFormulaTypeBasicFunction = std::bind(&PBPPModule<Settings>::checkFormulaTypeBasic, this, std::placeholders::_1);
            }

    template<class Settings>
        PBPPModule<Settings>::~PBPPModule()
        {}

    template<class Settings>
        bool PBPPModule<Settings>::informCore( const FormulaT& _constraint )
        {
            return true; // This should be adapted according to your implementation.
        }

    template<class Settings>
        void PBPPModule<Settings>::init()
        {}

    template<class Settings>
        bool PBPPModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
        {
            if (objective() != carl::Variable::NO_VARIABLE) {
                for (auto var: objectiveFunction().gatherVariables()) {
                    mVariablesCache.emplace(var, carl::freshBooleanVariable());
                }
            }
            if(Settings::use_rns_transformation){
                FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeWithRNSFunction);
                addSubformulaToPassedFormula(formula, _subformula->formula());
                return true;
            }else if(Settings::use_card_transformation){
                FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeWithCardConstrFunction);
                addSubformulaToPassedFormula(formula, _subformula->formula());
                return true;
            }else if(Settings::use_mixed_transformation){
                FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeWithMixedConstrFunction);
                addSubformulaToPassedFormula(formula, _subformula->formula());
                return true;
            }else if(Settings::use_basic_transformation){
                FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeBasicFunction);
                addSubformulaToPassedFormula(formula, _subformula->formula());
                return true;
            }else{
                FormulaT formula = mVisitor.visitResult(_subformula->formula(), checkFormulaTypeFunction);
                addSubformulaToPassedFormula(formula, _subformula->formula());
                return true;
            }
            return true;
        }

    template<class Settings>
        void PBPPModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
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


    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaType(const FormulaT& formula){
            // TODO we should probably make sure that we deal with pseudo boolean constraints
            if(formula.getType() != carl::FormulaType::CONSTRAINT){
                return formula;
            }

            const ConstraintT& c = formula.constraint();
            carl::Relation cRel = c.relation();
            const Poly& lhs = c.lhs();

            // TODO what does this mean?
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational rhs = lhs.constantPart(); // TODO extract constant or check whether we actually need it.
            Rational sum  = 0;
            Rational min = INT_MAX; // TODO I guess, this should be zero each. See TODO below
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

                // TODO this will only work if we find coefficients which exceed the integer limits
                if(it.coeff() < min){
                    min = it.coeff();
                }else if(it.coeff() > max){
                    max = it.coeff();
                }

                // sum monome coefficient
                sum += it.coeff();
            }

            for(std::size_t i = 0; i < lhsSize - 1; i++){
                // check whether the coefficients are all the same
                if(lhs[i].coeff() != lhs[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            // TODO what for? 
            ConstraintT constraint = changeVarTypeToBool(c);

            if(!positive && !negative){
                auto res = encodeMixedConstraints(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (lhs.lcoeff() == 1 || lhs.lcoeff() == -1 ) && lhsSize > 1){
                // x1 + x2 - x3 ~ b
                auto res = encodeCardinalityConstraint(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                // TODO only one term, probably this case will never be reached. 
                // TODO rename method. Yes, the formula is small
                auto res = convertSmallFormula(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(!(positive && rhs > 0 && sum > rhs
                        && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER || cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS))
                    &&  !(negative && rhs < 0 && (cRel == carl::Relation::GEQ || cRel == carl::Relation::GREATER) && sum < rhs)
                    && !(negative && rhs < 0 && (cRel == carl::Relation::LEQ || cRel == carl::Relation::LESS) && sum < rhs)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum != rhs && rhs != 0)
                    && !((positive || negative) && cRel == carl::Relation::NEQ && sum == rhs && rhs != 0)
                    && !(!positive && !negative)
                    ){
                // TODO rename method - what does big actually mean here?
                auto res = convertBigFormula(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeWithRNS(const FormulaT& formula){
            if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
                return FormulaT(formula);
            } 
            const ConstraintT& c = formula.constraint();
            carl::Relation cRel  = c.relation();
            const auto& cLHS = c.lhs();
            bool positive = true;
            Rational sum  = 0;
            bool isAllCoeffEqual = true;


            for(auto it = cLHS.begin(); it != cLHS.end(); it++){
                sum += it->coeff();
                if(it->coeff() < 0){
                    positive = false;
                }
            }

            for(std::size_t i = 0; i < cLHS.size() - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            // TODO refactor for Constraint
            ConstraintT constraint = changeVarTypeToBool(c);
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
            if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
                return FormulaT(formula);
            } 

            const ConstraintT& c = formula.constraint();
            carl::Relation cRel = c.relation();
            const auto& cLHS = c.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = c.constantPart();
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

            for(std::size_t i = 0; i < lhsSize - 1; i++){
                // TODO this might blow up if we check the constant term
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            ConstraintT constraint = changeVarTypeToBool(c);

            if(!positive && !negative){
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = encodeCardinalityConstraint(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;	
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint, c);
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
                auto res = convertBigFormula(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeWithMixedConstr(const FormulaT& formula){
            if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
                return FormulaT(formula);
            } 

            const ConstraintT& c = formula.constraint();
            carl::Relation cRel = c.relation();
            const auto& cLHS = c.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = c.constantPart();
            Rational sum  = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;
            // TODO substract 1 if we have a constant term
            std::size_t lhsSize = cLHS.size();

            ConstraintT constraint = changeVarTypeToBool(c);

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

            for(std::size_t i = 0; i < lhsSize - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = encodeMixedConstraints(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint, c);
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
                auto res = convertBigFormula(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::checkFormulaTypeBasic(const FormulaT& formula){
            if(formula.getType() != carl::FormulaType::PBCONSTRAINT){
                return FormulaT(formula);
            } 

            const ConstraintT& c = formula.constraint();
            carl::Relation cRel = c.relation();
            const auto& cLHS = c.lhs();
            bool positive = true;
            bool negative = true;
            bool isAllCoeffEqual = true;
            Rational cRHS = c.constantPart();
            Rational sum  = 0;
            Rational min = INT_MAX;
            Rational max = INT_MIN;
            // TODO substract 1 if we have a constant part
            std::size_t lhsSize = cLHS.size();

            ConstraintT constraint = changeVarTypeToBool(c);

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

            for(std::size_t i = 0; i < lhsSize - 1; i++){
                if(cLHS[i].coeff() != cLHS[i + 1].coeff()){
                    isAllCoeffEqual = false;
                    break;
                }
            }

            if(!positive && !negative){
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (cLHS.lcoeff() == 1 || cLHS.lcoeff() == -1 ) && lhsSize > 1){
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else if(lhsSize == 1){
                auto res = convertSmallFormula(constraint, c);
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
                auto res = convertBigFormula(constraint, c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }else{
                auto res = forwardAsArithmetic(c);
                SMTRAT_LOG_INFO("smtrat.pbc", formula << " -> " << res);
                return res;
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::encodeMixedConstraints(const ConstraintT& formula, const ConstraintT& c){
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
                        for(auto it : cLHS){
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
                            for(auto it : cLHS){
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
                            for(auto it : cLHS){
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
                            for(auto it : cLHS){
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
                            for(auto it : cLHS){
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
                    return convertBigFormula(changeVarTypeToBool(PBf), c);
                }else{
                    return forwardAsArithmetic(c);
                }
            }else{
                return forwardAsArithmetic(c);
            }
        }


    template<typename Settings>
        FormulaT PBPPModule<Settings>::encodeCardinalityConstraint(const ConstraintT& formula, const ConstraintT& c){
            const auto& cLHS = formula.lhs();
            auto cVars = formula.variables();
            Rational cRHS = formula.constantPart();
            carl::Relation cRel = formula.relation();
            // TODO lhsSize probably not correct
            std::size_t lhsSize = cLHS.size();
            Rational firstCoef = cLHS[0].coeff();
            Rational sum = 0;

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
                    for(std::size_t i = 0; i < lhsSize; i++){
                        FormulasT temp;
                        temp.push_back(FormulaT(cLHS[i].getSingleVariable()));
                        for(std::size_t j = 0; j < lhsSize; j++){
                            if(i != j){
                                temp.push_back(FormulaT(carl::FormulaType::NOT, FormulaT(cLHS[j].getSingleVariable())));
                            }
                        }
                        subformulasA.push_back(FormulaT(carl::FormulaType::AND, std::move(temp)));
                    }
                    FormulaT subformulaA = FormulaT(carl::FormulaType::OR, std::move(subformulasA));

                    FormulasT subformulasB;
                    for(auto it : cVars){
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
                            for(std::size_t i = 0; i < lhsSize; i++){
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
                    for(auto it : cVars){
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
                    for(auto it : cVars){
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
                        for(std::size_t i = 0; i < sign.size(); i++){
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
                            for(std::size_t i = 0; i < signs.size(); i++){
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


            for(auto it : cLHS){
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
            for(auto it : newLHS){
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
        FormulaT PBPPModule<Settings>::convertSmallFormula(const ConstraintT& formula, const ConstraintT& c){
            // TODO assert what small means here
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
        FormulaT PBPPModule<Settings>::convertBigFormula(const ConstraintT& formula, const ConstraintT& c){
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

            for(auto it : variables){
                mVariablesCache.insert(std::pair<carl::Variable, carl::Variable>(it, carl::freshBooleanVariable()));
            }

            Poly lhs;
            for(auto it : cLHS){
                // Poly pol(it.second);
                lhs = lhs + it.coeff() * it.getSingleVariable();
            }
            lhs = lhs - cRHS;
            FormulaT subformulaA = FormulaT(lhs, cRel);

            // Adding auxiliary constraint to ensure variables are assigned to 1 or 0.
            // FormulaT subformulaB = createAuxiliaryConstraint(variables);
            // FormulaT subformulaC = FormulaT(carl::FormulaType::AND, subformulaA, subformulaB);

            //Adding auxiliary constraint to interconnect the bool and int variables
            FormulaT subformulaD = interconnectVariables(variables);
            return FormulaT(carl::FormulaType::AND, subformulaA, subformulaD);
        }


    template<typename Settings>
        ConstraintT PBPPModule<Settings>::changeVarTypeToBool(const ConstraintT& formula){
            // this is actually the underlying polynomial
            const auto& cLHS = formula.lhs();
            carl::Relation cRel  = formula.relation();
            // TODO this does not exist! Instead, find the constant part of the formula.
            Rational cRHS = formula.constantPart();
            // TODO this is not the type for LHS
            Poly newLHS;
            // TODO check whether we actually need the variable cache.
            // For each monome,
            for(const auto& it : cLHS){
                auto finder = mVariablesCache.find(it.getSingleVariable());
                if(finder == mVariablesCache.end()){
                    // create a new bool variable
                    carl::Variable newVar = carl::freshBooleanVariable();
                    mVariablesCache.emplace(it.getSingleVariable(), newVar);
                    newLHS = newLHS + it.coeff() * newVar;
                } else {
                    newLHS = newLHS + it.coeff() * finder->second;
                }

            }

            // TODO substract cRHS from newLHS since constraints are always of the form lhs ~ 0

            return ConstraintT(newLHS, cRel);
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
