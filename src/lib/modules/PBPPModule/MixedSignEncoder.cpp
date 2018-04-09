#include "MixedSignEncoder.h"

namespace smtrat {
    boost::optional<FormulaT> MixedSignEncoder::encode(const ConstraintT& constraint) {
        carl::Relation cRel = constraint.relation();
        const Poly& cLHS = constraint.lhs();
        auto cVars = constraint.variables();
        Rational cRHS = constraint.constantPart();
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
                    }
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
                return mLongFormulaEncoder.encode(PBf);
            }
        }

        return {};
    }
}
