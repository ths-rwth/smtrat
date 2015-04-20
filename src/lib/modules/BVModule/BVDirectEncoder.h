/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file BVDirectEncoder.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 *
 * @version 2015-02-05
 * Created on 2015-02-05.
 */

#pragma once

#include "../../Common.h"
#include "carl/formula/bitvector/BVConstraint.h"
#include "carl/formula/bitvector/BVConstraintPool.h"

namespace smtrat
{
    class BVDirectEncoder
    {
        typedef carl::Variable Bit;
        typedef std::vector<carl::Variable> Bits;
        typedef carl::BVTerm BitVecTerm;
        typedef carl::BVConstraint BitVecConstr;
        typedef carl::BVVariable BitVec;
        typedef FormulaT Formula;

        private:
            std::map<BitVec, Bits> mBitVecToBits;
            std::map<Bit, BitVec> mBitToBitVec;

            std::map<BitVecTerm, Bits> mBits;
            std::list<Formula> mConstraints;

            Bit mConst0;
            Bit mConst1;

            const Bit const0()
            {
                return mConst0;
            }

            const Bit const1()
            {
                return mConst1;
            }

            void addConstraint(const Formula& _formula)
            {
                mConstraints.push_back(_formula);
            }

            Bits encodeConstant(const carl::BVValue& _value)
            {
                Bits out;

                for(size_t i=0;i<_value.size();++i)
                {
                    out.push_back(_value[i] ? const1() : const0());
                }

                return out;
            }

            Bits encodeVariable(const BitVec& _variable)
            {
                std::map<BitVec, Bits>::iterator it = mBitVecToBits.find(_variable);

                if(it == mBitVecToBits.end())
                {
                    Bits out = createBits(_variable.width());
                    mBitVecToBits[_variable] = out;
                    for(Bit bit: out) {
                        mBitToBitVec[bit] = _variable;
                    }
                    return out;
                }
                else
                {
                    return it->second;
                }
            }

            Bits encodeIte(const Bit& _condition, const Bits& _then, const Bits& _else)
            {
                Bits out = createBits(_then.size());

                for(std::size_t i=0;i<out.size();++i)
                {
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(out[i]),
                                          Formula(carl::FormulaType::ITE,
                                                  Formula(_condition),
                                                  Formula(_then[i]),
                                                  Formula(_else[i]))));
                }

                return out;
            }

            Bits encodeConcat(const Bits& _first, const Bits& _second)
            {
                Bits out(_second);
                out.insert(out.end(), _first.begin(), _first.end());

                return out;
            }

            Bits encodeExtract(const Bits& _operand, std::size_t _highest, std::size_t _lowest)
            {
                return Bits(&_operand[_lowest], &_operand[_highest+1]);
            }

            Bits encodeNot(const Bits& _operand)
            {
                Bits out = createBits(_operand.size());

                for(std::size_t i=0;i<out.size();++i)
                {
                    addConstraint(Formula(carl::FormulaType::XOR,
                                          Formula(_operand[i]),
                                          Formula(out[i])));
                }

                return out;
            }

            Bits encodeNeg(const Bits& _operand)
            {
                // Arithmetic negation = Bitwise negation + increment
                Bits negated = encodeNot(_operand);

                Bits carry = createBits(_operand.size() - 1);
                carry.insert(carry.begin(), const1());

                for(size_t i=1;i<_operand.size();++i)
                {
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(carry[i]),
                                          Formula(carl::FormulaType::AND,
                                                  Formula(carry[i-1]),
                                                  Formula(negated[i-1]))));
                }

                Bits out = createBits(_operand.size());

                for(size_t i=0;i<_operand.size();++i)
                {
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(out[i]),
                                          Formula(carl::FormulaType::XOR,
                                                  Formula(carry[i]),
                                                  Formula(negated[i]))));
                }

                return out;
            }

            Bits encodeAnd(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::AND, _first, _second);
            }

            Bits encodeOr(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::OR, _first, _second);
            }

            Bits encodeXor(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::XOR, _first, _second);
            }

            Bits encodeNand(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::NAND, _first, _second);
            }

            Bits encodeNor(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::NOR, _first, _second);
            }

            Bits encodeXnor(const Bits& _first, const Bits& _second)
            {
                return encodeLogicalBinary(carl::BVTermType::XNOR, _first, _second);
            }


            Bits encodeLogicalBinary(carl::BVTermType _type, const Bits& _first, const Bits& _second)
            {
                Bits out = createBits(_first.size());

                carl::FormulaType innerConnector;

                switch(_type)
                {
                    case carl::BVTermType::AND:
                    case carl::BVTermType::NAND:
                        innerConnector = carl::FormulaType::AND;
                        break;
                    case carl::BVTermType::OR:
                    case carl::BVTermType::NOR:
                        innerConnector = carl::FormulaType::OR;
                        break;
                    case carl::BVTermType::XOR:
                    case carl::BVTermType::XNOR:
                        innerConnector = carl::FormulaType::XOR;
                        break;
                    default:
                        assert(false);
                }

                carl::FormulaType outerConnector = carl::FormulaType::IFF;

                if(_type == carl::BVTermType::NAND || _type == carl::BVTermType::NOR || _type == carl::BVTermType::XNOR)
                {
                    outerConnector = carl::FormulaType::XOR;
                }

                for(size_t i=0;i<out.size();++i) {
                    addConstraint(
                        Formula(outerConnector,
                                 Formula(out[i]),
                                 Formula(innerConnector,
                                          Formula(_first[i]),
                                          Formula(_second[i])))
                    );
                }

                return out;
            }

            Bits encodeAdd(const Bits& _first, const Bits& _second)
            {
                return encodeAdderNetwork(_first, _second, false, false);
            }

            Bits encodeSub(const Bits& _first, const Bits& _second)
            {
                return encodeAdderNetwork(_first, encodeNot(_second), true);
            }

            Bits encodeAdderNetwork(const Bits& _first, const Bits& _second, bool _carryInValue = false, bool _withCarryOut = false)
            {
                Bits out = createBits(_first.size());
                Bits carry = createBits(_first.size() - (_withCarryOut ? 0 : 1));

                carry.insert(carry.begin(), (_carryInValue ? const1() : const0()));
                for(std::size_t i=1;i<carry.size();++i) {
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(carry[i]),
                                          Formula(carl::FormulaType::OR,
                                                  Formula(carl::FormulaType::AND,
                                                          Formula(_first[i-1]),
                                                          Formula(_second[i-1])),
                                                  Formula(carl::FormulaType::AND,
                                                          Formula(carl::FormulaType::XOR,
                                                                  Formula(_first[i-1]),
                                                                  Formula(_second[i-1])),
                                                          Formula(carry[i-1])))));
                }

                for(std::size_t i=0;i<out.size();++i) {
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(out[i]),
                                          Formula(carl::FormulaType::XOR,
                                                  Formula(_first[i]),
                                                  Formula(_second[i]),
                                                  Formula(carry[i]))));
                }

                return out;
            }

            Bits encodeMul(const Bits& _first, const Bits& _second)
            {
                std::vector<Bits> summands(_first.size());
                std::vector<Bits> sums(_first.size()-1);

                for(std::size_t i=0;i<summands.size();++i) {
                    summands[i] = createBits(_first.size() - i);

                    for(std::size_t j=0;j<summands[i].size();++i) {
                        addConstraint(Formula(carl::FormulaType::ITE,
                                              Formula(_second[i]),
                                              Formula(_first[j]),
                                              Formula(carl::FormulaType::FALSE)));
                    }
                    summands[i].insert(summands[i].begin(), i, const0());
                }

                for(std::size_t i=0;i<sums.size();++i) {
                    sums[i] = encodeAdderNetwork(summands[i], summands[i+1]);
                }

                if(sums.size() > 0) {
                    return sums[sums.size()-1];
                } else {
                    return summands[0];
                }
            }

            Bits encodeDivU(const Bits& _first, const Bits& _second)
            {
                return encodeDivisionNetwork(_first, _second, false);
            }

            Bits encodeDivisionNetwork(const Bits& _first, const Bits& _second, bool _returnRemainder = false)
            {
                Bits out;
                Bits remainder;

                Bit wellDefined = encodeNeq(_second, encodeConstant(carl::BVValue(_second.size(), 0)));

                Bit summationCorrect = encodeEq(
                    _first,
                    encodeAdd(
                        encodeMul(out, _second),
                        remainder
                    )
                );

                Bit remainderLessThanDivisor = encodeUlt(remainder, _second);

                addConstraint(Formula(carl::FormulaType::IMPLIES,
                                      Formula(wellDefined),
                                      Formula(carl::FormulaType::AND,
                                              Formula(summationCorrect),
                                              Formula(remainderLessThanDivisor))));

                return (_returnRemainder ? remainder : out);
            }

            Bits encodeDivS(const Bits& _first, const Bits& _second)
            {
                /*
                (bvsdiv s t) abbreviates
                (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                        (?msb_t ((_ extract |m-1| |m-1|) t)))
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                        (bvudiv s t)
                    (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                        (bvneg (bvudiv (bvneg s) t))
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                        (bvneg (bvudiv s (bvneg t)))
                        (bvudiv (bvneg s) (bvneg t))))))
                */
                Bit msbFirst = _first[_first.size()-1];
                Bit msbSecond = _second[_second.size()-1];

                return encodeIte(msbFirst,
                                 encodeIte(msbSecond,
                                           encodeDivU(encodeNeg(_first), encodeNeg(_second)),
                                           encodeNeg(encodeDivU(encodeNeg(_first), _second))),
                                 encodeIte(msbSecond,
                                           encodeNeg(encodeDivU(_first, encodeNeg(_second))),
                                           encodeDivU(_first, _second)));
            }

            Bits encodeModU(const Bits& _first, const Bits& _second)
            {
                return encodeDivisionNetwork(_first, _second, true);
            }

            Bits encodeModS1(const Bits& _first, const Bits& _second)
            {
                /*
                (bvsrem s t) abbreviates
                (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                        (?msb_t ((_ extract |m-1| |m-1|) t)))
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                        (bvurem s t)
                    (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                        (bvneg (bvurem (bvneg s) t))
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                        (bvurem s (bvneg t)))
                        (bvneg (bvurem (bvneg s) (bvneg t))))))
                */
                Bit msbFirst = _first[_first.size()-1];
                Bit msbSecond = _second[_second.size()-1];

                return encodeIte(msbFirst,
                                 encodeIte(msbSecond,
                                           encodeNeg(encodeModU(encodeNeg(_first), encodeNeg(_second))),
                                           encodeNeg(encodeModU(encodeNeg(_first), _second))),
                                 encodeIte(msbSecond,
                                           encodeModU(_first, encodeNeg(_second)),
                                           encodeModU(_first, _second)));
            }

            Bits encodeModS2(const Bits& _first, const Bits& _second)
            {
                /*
                (bvsmod s t) abbreviates
                (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                        (?msb_t ((_ extract |m-1| |m-1|) t)))
                    (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
                        (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
                    (let ((u (bvurem abs_s abs_t)))
                        (ite (= u (_ bv0 m))
                            u
                        (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                            u
                        (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                            (bvadd (bvneg u) t)
                        (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                            (bvadd u t)
                            (bvneg u))))))))
                */
                Bit msbFirst = _first[_first.size()-1];
                Bit msbSecond = _second[_second.size()-1];

                Bits absFirst = encodeIte(msbFirst, encodeNeg(_first), _first);
                Bits absSecond = encodeIte(msbSecond, encodeNeg(_second), _second);

                Bits u = encodeModU(absFirst, absSecond);

                return encodeIte(encodeEq(u, encodeConstant(carl::BVValue(_first.size(), 0))),
                                 u,
                                 encodeIte(msbFirst,
                                           encodeIte(msbSecond,
                                                     encodeNeg(u),
                                                     encodeAdd(encodeNeg(u), _second)),
                                           encodeIte(msbSecond,
                                                     encodeAdd(u, _second),
                                                     u)));
            }

            Bits encodeComp(const Bits& _first, const Bits& _second)
            {
                Bits out;
                out.push_back(encodeEq(_first, _second));
                return out;
            }

            Bits encodeLshift(const Bits& _first, const Bits& _second)
            {
                return encodeShiftNetwork(_first, _second, true);
            }

            Bits encodeShiftNetwork(const Bits& _first, const Bits& _second, bool _left, bool _fillWith = false)
            {
                std::size_t firstSize = _first.size() - 1;
                std::size_t highestRelevantPos = 0;

                while((firstSize >>= 1) != 0)
                    ++highestRelevantPos;

                Bits lastStage(_first);
                std::size_t currentShiftBy = 0;

                for(std::size_t stage=0;stage<=highestRelevantPos && stage<_second.size();++stage)
                {
                    ++currentShiftBy;
                    Bits currentStage = createBits(lastStage.size());

                    for(std::size_t pos=0;pos<lastStage.size();++pos)
                    {
                        Bit notShifted = lastStage[pos];
                        Bit shifted;

                        if((_left && pos >= currentShiftBy) || (! _left && pos + currentShiftBy < lastStage.size()))
                        {
                            shifted = lastStage[_left ? (pos - currentShiftBy) : (pos + currentShiftBy)];
                        }
                        else
                        {
                            shifted = _fillWith ? const1() : const0();
                        }

                        addConstraint(Formula(carl::FormulaType::IFF,
                                              Formula(currentStage[pos]),
                                              Formula(carl::FormulaType::ITE,
                                                      Formula(_second[stage]),
                                                      Formula(shifted),
                                                      Formula(notShifted))));
                    }

                    lastStage = currentStage;
                }

                if(highestRelevantPos >= _second.size() - 1)
                {
                    return lastStage;
                }
                else
                {
                    Bits out = createBits(_first.size());

                    std::vector<Formula> subFormulas;
                    for(std::size_t pos=highestRelevantPos+1;pos<_second.size();++pos)
                    {
                        subFormulas.push_back(Formula(_second[pos]));
                    }

                    Bit shiftOut = createBit();
                    addConstraint(Formula(carl::FormulaType::IFF,
                                          Formula(shiftOut),
                                          Formula(carl::FormulaType::OR, subFormulas)));

                    for(std::size_t i=0;i<out.size();++i)
                    {
                        addConstraint(Formula(carl::FormulaType::IFF,
                                              Formula(out[i]),
                                              Formula(carl::FormulaType::ITE,
                                                      Formula(shiftOut),
                                                      Formula(_fillWith ? const1() : const0()),
                                                      Formula(lastStage[i]))));
                    }

                    return out;
                }
            }

            Bits encodeRshiftLogic(const Bits& _first, const Bits& _second)
            {
                return encodeShiftNetwork(_first, _second, false);
            }

            Bits encodeRshiftArith(const Bits& _first, const Bits& _second)
            {
                return encodeShiftNetwork(_first, _second, false, true);
            }

            Bits encodeLrotate(const Bits& _operand, std::size_t _index)
            {
                Bits out(_operand);
                std::rotate(out.begin(),
                            out.begin() + (Bits::difference_type)(
                                _index % _operand.size()),
                            out.end());
                return out;
            }

            Bits encodeRrotate(const Bits& _operand, std::size_t _index)
            {
                Bits out(_operand);
                std::rotate(out.begin(),
                            out.begin() + (Bits::difference_type)(
                                (_operand.size() -
                                    (_index % _operand.size()))
                                % _operand.size()),
                            out.end());
                return out;
            }

            Bits encodeExtU(const Bits& _operand, std::size_t _index)
            {
                Bits out(_operand);
                out.insert(out.end(), _index, const0());
                return out;
            }

            Bits encodeExtS(const Bits& _operand, std::size_t _index)
            {
                Bits out(_operand);
                out.insert(out.end(), _index, _operand[_operand.size()-1]);
                return out;
            }

            Bits encodeRepeat(const Bits& _operand, std::size_t _index)
            {
                Bits out;
                for(std::size_t i=0;i<_index;++i)
                {
                    out.insert(out.end(), _operand.begin(), _operand.end());
                }
                return out;
            }

            Bits encodeTerm(const BitVecTerm& _term)
            {
                auto it = mBits.find(_term);
                if(it != mBits.end()) {
                    return it->second;
                }

                Bits result;
                Bits subTerm1;
                Bits subTerm2;
                carl::BVTermType type = _term.type();

                if(carl::typeIsUnary(type) || type == carl::BVTermType::EXTRACT) {
                    subTerm1 = encodeTerm(_term.operand());
                }
                else if(carl::typeIsBinary(type)) {
                    subTerm1 = encodeTerm(_term.first());
                    subTerm2 = encodeTerm(_term.second());
                }

                switch(type) {
                    case carl::BVTermType::CONSTANT:
                        result = encodeConstant(_term.value()); break;
                    case carl::BVTermType::VARIABLE:
                        result = encodeVariable(_term.variable()); break;
                    case carl::BVTermType::CONCAT:
                        result = encodeConcat(subTerm1, subTerm2); break;
                    case carl::BVTermType::EXTRACT:
                        result = encodeExtract(subTerm1, _term.highest(), _term.lowest()); break;
                    case carl::BVTermType::NOT:
                        result = encodeNot(subTerm1); break;
                    case carl::BVTermType::NEG:
                        result = encodeNeg(subTerm1); break;
                    case carl::BVTermType::AND:
                        result = encodeAnd(subTerm1, subTerm2); break;
                    case carl::BVTermType::OR:
                        result = encodeOr(subTerm1, subTerm2); break;
                    case carl::BVTermType::XOR:
                        result = encodeXor(subTerm1, subTerm2); break;
                    case carl::BVTermType::NAND:
                        result = encodeNand(subTerm1, subTerm2); break;
                    case carl::BVTermType::NOR:
                        result = encodeNor(subTerm1, subTerm2); break;
                    case carl::BVTermType::XNOR:
                        result = encodeXnor(subTerm1, subTerm2); break;
                    case carl::BVTermType::ADD:
                        result = encodeAdd(subTerm1, subTerm2); break;
                    case carl::BVTermType::SUB:
                        result = encodeSub(subTerm1, subTerm2); break;
                    case carl::BVTermType::MUL:
                        result = encodeMul(subTerm1, subTerm2); break;
                    case carl::BVTermType::DIV_U:
                        result = encodeDivU(subTerm1, subTerm2); break;
                    case carl::BVTermType::DIV_S:
                        result = encodeDivS(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_U:
                        result = encodeModU(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_S1:
                        result = encodeModS1(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_S2:
                        result = encodeModS2(subTerm1, subTerm2); break;
                    case carl::BVTermType::EQ:
                        result = encodeComp(subTerm1, subTerm2); break;
                    case carl::BVTermType::LSHIFT:
                        result = encodeLshift(subTerm1, subTerm2); break;
                    case carl::BVTermType::RSHIFT_LOGIC:
                        result = encodeRshiftLogic(subTerm1, subTerm2); break;
                    case carl::BVTermType::RSHIFT_ARITH:
                        result = encodeRshiftArith(subTerm1, subTerm2); break;
                    case carl::BVTermType::LROTATE:
                        result = encodeLrotate(subTerm1, _term.index()); break;
                    case carl::BVTermType::RROTATE:
                        result = encodeRrotate(subTerm1, _term.index()); break;
                    case carl::BVTermType::EXT_U:
                        result = encodeExtU(subTerm1, _term.index()); break;
                    case carl::BVTermType::EXT_S:
                        result = encodeExtS(subTerm1, _term.index()); break;
                    case carl::BVTermType::REPEAT:
                        result = encodeRepeat(subTerm1, _term.index()); break;
                    default:
                        assert(false);
                }

                mBits[_term] = result;
                return result;
            }

            Bit encodeConstraint(const BitVecConstr& _constraint)
            {
                Bits lhs = encodeTerm(_constraint.lhs());
                Bits rhs = encodeTerm(_constraint.rhs());

                carl::BVCompareRelation relation = _constraint.relation();

                switch(relation)
                {
                    case carl::BVCompareRelation::EQ:
                        return encodeEq(lhs, rhs); break;
                    case carl::BVCompareRelation::NEQ:
                        return encodeNeq(lhs, rhs); break;
                    case carl::BVCompareRelation::ULT:
                        return encodeUlt(lhs, rhs); break;
                    case carl::BVCompareRelation::ULE:
                        return encodeUle(lhs, rhs); break;
                    case carl::BVCompareRelation::UGT:
                        return encodeUgt(lhs, rhs); break;
                    case carl::BVCompareRelation::UGE:
                        return encodeUge(lhs, rhs); break;
                    case carl::BVCompareRelation::SLT:
                        return encodeSlt(lhs, rhs); break;
                    case carl::BVCompareRelation::SLE:
                        return encodeSle(lhs, rhs); break;
                    case carl::BVCompareRelation::SGT:
                        return encodeSgt(lhs, rhs); break;
                    case carl::BVCompareRelation::SGE:
                        return encodeSge(lhs, rhs); break;
                }

                assert(false);
                return Bit();
            }

            Bit encodeEq(const Bits& _lhs, const Bits& _rhs)
            {
                Bit out = createBit();
                std::vector<Formula> subFormulas;

                for(std::size_t i=0;i<_lhs.size();++i)
                {
                    subFormulas.push_back(Formula(carl::FormulaType::IFF,
                                                  Formula(_lhs[i]),
                                                  Formula(_rhs[i])));
                }

                addConstraint(Formula(carl::FormulaType::IFF,
                                      Formula(out),
                                      Formula(carl::FormulaType::AND, subFormulas)));
                return out;
            }

            Bit encodeNeq(const Bits& _lhs, const Bits& _rhs)
            {
                return encodeInverse(encodeEq(_lhs, _rhs));
            }

            Bit encodeUlt(const Bits& _lhs, const Bits& _rhs)
            {
                return encodeInverse(encodeUge(_lhs, _rhs));
            }

            Bit encodeUle(const Bits& _lhs, const Bits& _rhs)
            {
                Bit ult = encodeUlt(_lhs, _rhs);
                Bit eq = encodeEq(_lhs, _rhs);
                Bit out = createBit();
                addConstraint(Formula(carl::FormulaType::IFF,
                                      Formula(out),
                                      Formula(carl::FormulaType::OR,
                                              Formula(eq),
                                              Formula(ult))));
                return out;
            }

            Bit encodeUgt(const Bits& _lhs, const Bits& _rhs)
            {
                return encodeInverse(encodeUle(_lhs, _rhs));
            }

            Bit encodeUge(const Bits& _lhs, const Bits& _rhs)
            {
                Bits addition = encodeAdderNetwork(_lhs, encodeNot(_rhs), true, true);
                return addition[addition.size()-1];
            }

            Bit encodeSlt(const Bits& _lhs, const Bits& _rhs)
            {
                /*
                (bvslt s t) abbreviates:
                (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
                        (= ((_ extract |m-1| |m-1|) t) #b0))
                    (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
                        (bvult s t)))
                */
                Bit msbLhs = _lhs[_lhs.size()-1];
                Bit msbRhs = _rhs[_rhs.size()-1];
                Bit ult = encodeUlt(_lhs, _rhs);
                Bit out = createBit();

                addConstraint(Formula(carl::FormulaType::IFF,
                                      Formula(out),
                                      Formula(carl::FormulaType::OR,
                                              Formula(carl::FormulaType::AND,
                                                      Formula(msbLhs),
                                                      Formula(carl::FormulaType::NOT, Formula(msbRhs))),
                                              Formula(carl::FormulaType::AND,
                                                      Formula(carl::FormulaType::IFF,
                                                              Formula(msbLhs),
                                                              Formula(msbRhs)),
                                                      Formula(ult)))));
                return out;
            }

            Bit encodeSle(const Bits& _lhs, const Bits& _rhs)
            {
                /*
                (bvsle s t) abbreviates:
                (or (and (= ((_ extract |m-1| |m-1|) s) #b1)
                        (= ((_ extract |m-1| |m-1|) t) #b0))
                    (and (= ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
                        (bvule s t)))
                */
                Bit msbLhs = _lhs[_lhs.size()-1];
                Bit msbRhs = _rhs[_rhs.size()-1];
                Bit ule = encodeUle(_lhs, _rhs);
                Bit out = createBit();

                addConstraint(Formula(carl::FormulaType::IFF,
                                      Formula(out),
                                      Formula(carl::FormulaType::OR,
                                              Formula(carl::FormulaType::AND,
                                                      Formula(msbLhs),
                                                      Formula(carl::FormulaType::NOT, Formula(msbRhs))),
                                              Formula(carl::FormulaType::AND,
                                                      Formula(carl::FormulaType::IFF,
                                                              Formula(msbLhs),
                                                              Formula(msbRhs)),
                                                      Formula(ule)))));
                return out;
            }

            Bit encodeSgt(const Bits& _lhs, const Bits& _rhs)
            {
                return encodeInverse(encodeSle(_lhs, _rhs));
            }

            Bit encodeSge(const Bits& _lhs, const Bits& _rhs)
            {
                return encodeInverse(encodeSlt(_lhs, _rhs));
            }

            Bit encodeInverse(const Bit& _original)
            {
                Bit out = createBit();
                addConstraint(Formula(carl::FormulaType::XOR, Formula(_original), Formula(out)));
                return out;
            }

            Bit createBit()
            {
                return carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_BOOL);
            }

            Bits createBits(std::size_t _n)
            {
                Bits out(_n);

                for(std::size_t i=0;i<_n;++i) {
                    out[i] = createBit();
                }

                return out;
            }


        public:

            void encode(const BitVecConstr& _constraint)
            {
                Bit out = encodeConstraint(_constraint);
                addConstraint(Formula(out));
            }

            std::list<Formula> toSAT()
            {
                return mConstraints;
            }

            BVDirectEncoder() : mBitVecToBits(), mBitToBitVec(), mBits(), mConstraints()
            {
                mConst0 = createBit();
                mConst1 = createBit();

                addConstraint(Formula(mConst1));
                addConstraint(Formula(carl::FormulaType::NOT, Formula(mConst0)));
            }

            ~BVDirectEncoder()
            {}

    };
}
