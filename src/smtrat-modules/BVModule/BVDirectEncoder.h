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

#define SMTRAT_BV_INCREMENTAL_MODE
// define SMTRAT_BV_ENCODER_DEBUG

#include <smtrat-common/smtrat-common.h>
#include <carl-formula/bitvector/BVConstraint.h>
#include <carl-formula/bitvector/BVConstraintPool.h>

namespace smtrat
{
    class BVDirectEncoder
    {
        typedef carl::Variable Variable;
        typedef std::vector<Variable> Variables;
        typedef FormulaT Bit;
        typedef std::vector<Bit> Bits;
        typedef carl::BVTerm BitVecTerm;
        typedef carl::BVConstraint BitVecConstr;
        typedef carl::BVVariable BitVec;
        typedef FormulaT Formula;

        private:
            // Set of all propositional variables that have been introduced by the encoder
            std::set<Variable> mIntroducedVariables;

            // Substituted fresh variables
            //  - for bitvector variables (one variable for each bitvector bit)
            carl::FastMap<BitVec, Variables> mBitVecBits;
            //  - for bitvector terms (likewise, one variable for each bitvector bit)
            carl::FastMap<BitVecTerm, Bits> mTermBits;
            //  - for bitvector constraints (a single variable)
            carl::FastMap<BitVecConstr, Bit> mConstraintBits;

            // Created formulas ("encodings")

            #ifdef SMTRAT_BV_INCREMENTAL_MODE
            //  - for terms
            carl::FastMap<BitVecTerm, FormulaSetT> mTermEncodings;
            //  - for constraints (not including the encodings for the contained terms)
            carl::FastMap<BitVecConstr, FormulaSetT> mConstraintEncodings;
            #endif
            //  - for terms and constraints originating from the current input formula
            FormulaSetT mCurrentEncodings;

            // Encoding state (remember currently encoded constraint/term)
            std::optional<BitVecConstr> mCurrentConstraint;
            std::optional<BitVecTerm> mCurrentTerm;

            /*
            Bit mConst0;
            Bit mConst1;
            */

            const Bit const0()
            {
                return createBit(FormulaT(carl::FormulaType::FALSE));
                /* boolAssert(boolNot(mConst0));
                return mConst0; */
            }

            const Bit const1()
            {
                return createBit(FormulaT(carl::FormulaType::TRUE));
                /* boolAssert(mConst1);
                return mConst1; */
            }

            void boolAssert(const Formula& _formula)
            {
                #ifdef SMTRAT_BV_INCREMENTAL_MODE
                if(mCurrentTerm) {
                    mTermEncodings.insert(std::make_pair(*mCurrentTerm, FormulaSetT()));
                    mTermEncodings[*mCurrentTerm].insert(_formula);
                } else if(mCurrentConstraint) {
                    mConstraintEncodings.insert(std::make_pair(*mCurrentConstraint, FormulaSetT()));
                    mConstraintEncodings[*mCurrentConstraint].insert(_formula);
                }
                #endif

                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << " -> " << _formula << std::endl;
                #endif
                mCurrentEncodings.insert(_formula);
            }

            Bits encodeConstant(const carl::BVValue& _value)
            {
                Bits out;
                for(size_t i=0;i<_value.width();++i)
                {
                    out.push_back(_value[i] ? const1() : const0());
                }
                return out;
            }

            Bits encodeVariable(const BitVec& _variable)
            {
                Variables boolVariables;
                carl::FastMap<BitVec, Variables>::iterator it = mBitVecBits.find(_variable);

                if(it == mBitVecBits.end())
                {
                    boolVariables = createVariables(_variable.width());
                    mBitVecBits[_variable] = boolVariables;
                }
                else
                {
                    boolVariables = it->second;
                }

                return createBits(boolVariables);
            }

            Bits encodeIte(const Bit& _condition, const Bits& _then, const Bits& _else)
            {
                Bits out;
                for(std::size_t i=0;i<_then.size();++i)
                {
                    out.push_back(createBit(boolIte(_condition, _then[i], _else[i])));
                }
                return out;
            }

            Bits encodeConcat(const Bits& _first, const Bits& _second)
            {
                Bits concatenated(_second);
                concatenated.insert(concatenated.end(), _first.begin(), _first.end());
                return createBits(concatenated);
            }

            Bits encodeExtract(const Bits& _operand, std::size_t _highest, std::size_t _lowest)
            {
                return createBits(Bits(&_operand[_lowest], &_operand[_highest+1]));
            }

            Bits encodeNot(const Bits& _operand)
            {
                Bits out;
                for(const Bit& bit : _operand) {
                    out.push_back(createBit(boolNot(bit)));
                }
                return out;
            }

            Bits encodeNeg(const Bits& _operand)
            {
                // Arithmetic negation = Bitwise negation + increment
                Bits negated = encodeNot(_operand);

                Bits carry;
                carry.push_back(const1());

                for(size_t i=1;i<_operand.size();++i)
                {
                    carry.push_back(createBit(boolAnd(carry[i-1], negated[i-1])));
                }

                Bits out;

                for(size_t i=0;i<_operand.size();++i)
                {
                    out.push_back(createBit(boolXor(carry[i], negated[i])));
                }

                return out;
            }

            Bits encodeAnd(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolAnd(_first[i], _second[i])));
                }
                return out;
            }

            Bits encodeOr(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolOr(_first[i], _second[i])));
                }
                return out;
            }

            Bits encodeXor(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolXor(_first[i], _second[i])));
                }
                return out;
            }

            Bits encodeNand(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolNot(boolAnd(_first[i], _second[i]))));
                }
                return out;
            }

            Bits encodeNor(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolNot(boolOr(_first[i], _second[i]))));
                }
                return out;
            }

            Bits encodeXnor(const Bits& _first, const Bits& _second)
            {
                Bits out;
                for(std::size_t i = 0; i < _first.size(); ++i) {
                    out.push_back(createBit(boolIff(_first[i], _second[i])));
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

            Bits encodeAdderNetwork(const Bits& _first, const Bits& _second, bool _carryInValue = false, bool _withCarryOut = false, bool _allowOverflow = true)
            {
                Bits out;
                Bits carry;

                carry.push_back(_carryInValue ? const1() : const0());
                std::size_t carryBitCount = _first.size() + ((_withCarryOut || ! _allowOverflow) ? 1 : 0);

                for(std::size_t i=1;i<carryBitCount;++i) {
                    carry.push_back(createBit(
                        boolOr(
                            boolAnd(_first[i-1], _second[i-1]),
                            boolAnd(
                                boolXor(_first[i-1], _second[i-1]),
                                carry[i-1]
                            )
                        )
                    ));
                }

                for(std::size_t i=0;i<_first.size();++i) {
                    out.push_back(createBit(
                        boolXor(_first[i], boolXor(_second[i], carry[i]))
                    ));
                }

                if(! _allowOverflow) {
                    boolAssert(boolNot(carry[carry.size()-1]));
                }
                if(_withCarryOut) {
                    out.push_back(carry[carry.size()-1]);
                }

                return out;
            }

            Bits encodeMul(const Bits& _first, const Bits& _second)
            {
                return encodeMultiplicationNetwork(_first, _second);
            }

            Bits encodeMultiplicationNetwork(const Bits& _first, const Bits& _second, bool _allowOverflow = true)
            {
                std::vector<Bits> summands(_first.size());
                std::vector<Bits> sums(_first.size()-1);

                for(std::size_t i=0;i<summands.size();++i) {
                    for(std::size_t j=0;j<_first.size();++j) {
                        if(j < i) {
                            summands[i].push_back(const0());
                        } else {
                            summands[i].push_back(createBit(boolAnd(_second[i], _first[j-i])));
                        }
                    }

                    if(! _allowOverflow) {
                        for(std::size_t j=_first.size();j<_first.size()+i;++j) {
                            boolAssert(boolNot(boolAnd(_second[i], _first[j-i])));
                        }
                    }
                }

                for(std::size_t i=0;i<sums.size();++i) {
                    sums[i] = encodeAdderNetwork((i == 0 ? summands[0] : sums[i-1]), summands[i+1], false, false, _allowOverflow);
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
                Bits quotient = createBits(_first.size());
                Bits remainder = createBits(_first.size());

                Bit wellDefined = boolOr(_second);

                Bit summationCorrect = encodeEq(
                    _first,
                    encodeAdderNetwork(
                        encodeMultiplicationNetwork(quotient, _second, false),
                        remainder,
                        false,
                        false,
                        false
                    )
                );

                Bit remainderLessThanDivisor = encodeUlt(remainder, _second);

                boolAssert(boolImplies(wellDefined, boolAnd(summationCorrect, remainderLessThanDivisor)));
				if (!_returnRemainder) {
					// bvudiv: x / 0 = 111...
					/// TODO: Create a direct encoding of this instead of an equation to a constant.
					Bit quotientAllOnes = encodeEq(quotient, encodeConstant(~carl::BVValue(_first.size(), 0)));
					boolAssert(boolImplies(!wellDefined, quotientAllOnes));
				} else {
					// mvurem: x / 0 = x
					Bit remainderIsFirstOp = encodeEq(remainder, _first);
					boolAssert(boolImplies(!wellDefined, remainderIsFirstOp));
				}

                return (_returnRemainder ? remainder : quotient);
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

                return encodeIte(boolNot(boolOr(u)),
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

            Bits encodeShiftNetwork(const Bits& _first, const Bits& _second, bool _left, bool _arithmetic = false)
            {
                std::size_t firstSize = _first.size() - 1;
                std::size_t highestRelevantPos = 0;

                while((firstSize >>= 1) != 0)
                    ++highestRelevantPos;

                Bits lastStage(_first);
                std::size_t currentShiftBy = 1;

                for(std::size_t stage=0;stage<=highestRelevantPos && stage<_second.size();++stage)
                {
                    Bits currentStage;

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
                            shifted = _arithmetic ? _first[_first.size() - 1] : const0();
                        }

                        currentStage.push_back(createBit(boolIte(_second[stage], shifted, notShifted)));
                    }

                    currentShiftBy *= 2;
                    lastStage = currentStage;
                }

                if(highestRelevantPos >= _second.size() - 1)
                {
                    return lastStage;
                }
                else
                {
                    Bits overshiftBits(&_second[highestRelevantPos+1], &_second[_second.size()]);
                    Bit overshift = boolOr(overshiftBits);

                    Bits out;

                    for(std::size_t i=0;i<_first.size();++i)
                    {
                        out.push_back(createBit(
                            boolIte(overshift, (_arithmetic ? _first[_first.size()-1] : const0()), lastStage[i])
                        ));
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
                Bits rotated(_operand);
                std::rotate(rotated.begin(),
                            rotated.begin() + (Bits::difference_type)(
                                (_operand.size() -
                                    (_index % _operand.size()))
                                % _operand.size()),
                            rotated.end());
                return createBits(rotated);
            }

            Bits encodeRrotate(const Bits& _operand, std::size_t _index)
            {
                Bits rotated(_operand);
                std::rotate(rotated.begin(),
                            rotated.begin() + (Bits::difference_type)(
                                _index % _operand.size()),
                            rotated.end());
                return createBits(rotated);
            }

            Bits encodeExtU(const Bits& _operand, std::size_t _index)
            {
                Bits out = createBits(_operand);
                for(std::size_t i=0;i<_index;++i) {
                    out.push_back(const0());
                }
                return out;
            }

            Bits encodeExtS(const Bits& _operand, std::size_t _index)
            {
                Bits out = createBits(_operand);
                for(std::size_t i=0;i<_index;++i) {
                    out.push_back(createBit(_operand[_operand.size()-1]));
                }
                return out;
            }

            Bits encodeRepeat(const Bits& _operand, std::size_t _index)
            {
                Bits repeated;
                for(std::size_t i=0;i<_index;++i)
                {
                    repeated.insert(repeated.end(), _operand.begin(), _operand.end());
                }
                return createBits(repeated);
            }

            Bits encodeTerm(const BitVecTerm& _term)
            {
                #ifndef SMTRAT_BV_INCREMENTAL_MODE
                auto it = mTermBits.find(_term);
                if(it != mTermBits.end()) {
                    return it->second;
                }
                #endif

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

                #ifdef SMTRAT_BV_INCREMENTAL_MODE
                auto it = mTermEncodings.find(_term);
                if(it != mTermEncodings.end())
                {
                    mCurrentEncodings.insert(it->second.begin(), it->second.end());
                    return mTermBits[_term];
                }
                #endif

                // The term has not been encoded yet. Encode it now
                mCurrentTerm = _term;
                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << "[BV] Encoding term: " << _term << std::endl;
                #endif
                Bits out;

                switch(type) {
                    case carl::BVTermType::CONSTANT:
                        out = encodeConstant(_term.value()); break;
                    case carl::BVTermType::VARIABLE:
                        out = encodeVariable(_term.variable()); break;
                    case carl::BVTermType::CONCAT:
                        out = encodeConcat(subTerm1, subTerm2); break;
                    case carl::BVTermType::EXTRACT:
                        out = encodeExtract(subTerm1, _term.highest(), _term.lowest()); break;
                    case carl::BVTermType::NOT:
                        out = encodeNot(subTerm1); break;
                    case carl::BVTermType::NEG:
                        out = encodeNeg(subTerm1); break;
                    case carl::BVTermType::AND:
                        out = encodeAnd(subTerm1, subTerm2); break;
                    case carl::BVTermType::OR:
                        out = encodeOr(subTerm1, subTerm2); break;
                    case carl::BVTermType::XOR:
                        out = encodeXor(subTerm1, subTerm2); break;
                    case carl::BVTermType::NAND:
                        out = encodeNand(subTerm1, subTerm2); break;
                    case carl::BVTermType::NOR:
                        out = encodeNor(subTerm1, subTerm2); break;
                    case carl::BVTermType::XNOR:
                        out = encodeXnor(subTerm1, subTerm2); break;
                    case carl::BVTermType::ADD:
                        out = encodeAdd(subTerm1, subTerm2); break;
                    case carl::BVTermType::SUB:
                        out = encodeSub(subTerm1, subTerm2); break;
                    case carl::BVTermType::MUL:
                        out = encodeMul(subTerm1, subTerm2); break;
                    case carl::BVTermType::DIV_U:
                        out = encodeDivU(subTerm1, subTerm2); break;
                    case carl::BVTermType::DIV_S:
                        out = encodeDivS(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_U:
                        out = encodeModU(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_S1:
                        out = encodeModS1(subTerm1, subTerm2); break;
                    case carl::BVTermType::MOD_S2:
                        out = encodeModS2(subTerm1, subTerm2); break;
                    case carl::BVTermType::EQ:
                        out = encodeComp(subTerm1, subTerm2); break;
                    case carl::BVTermType::LSHIFT:
                        out = encodeLshift(subTerm1, subTerm2); break;
                    case carl::BVTermType::RSHIFT_LOGIC:
                        out = encodeRshiftLogic(subTerm1, subTerm2); break;
                    case carl::BVTermType::RSHIFT_ARITH:
                        out = encodeRshiftArith(subTerm1, subTerm2); break;
                    case carl::BVTermType::LROTATE:
                        out = encodeLrotate(subTerm1, _term.index()); break;
                    case carl::BVTermType::RROTATE:
                        out = encodeRrotate(subTerm1, _term.index()); break;
                    case carl::BVTermType::EXT_U:
                        out = encodeExtU(subTerm1, _term.index()); break;
                    case carl::BVTermType::EXT_S:
                        out = encodeExtS(subTerm1, _term.index()); break;
                    case carl::BVTermType::REPEAT:
                        out = encodeRepeat(subTerm1, _term.index()); break;
                    default:
                        assert(false);
                }

                mTermBits[_term] = out;
                mCurrentTerm = std::nullopt;

                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << "Encoded into:";
                for(auto bIt = out.crbegin(); bIt != out.crend(); ++bIt) {
                    std::cerr << " <" << *bIt << ">";
                }
                std::cerr << std::endl;
                #endif

                return out;
            }

            Bit encodeConstraint(const BitVecConstr& _constraint)
            {
                #ifndef SMTRAT_BV_INCREMENTAL_MODE
                auto it = mConstraintBits.find(_constraint);
                if(it != mConstraintBits.end()) {
                    return it->second;
                }
                #endif

                // In incremental mode,
                // always call encodeTerm() on both subterms, even if we have
                // already encoded _constraint. This way the mCurrentEncodings
                // set is built correctly.
                Bits lhs = encodeTerm(_constraint.lhs());
                Bits rhs = encodeTerm(_constraint.rhs());

                #ifdef SMTRAT_BV_INCREMENTAL_MODE
                auto it = mConstraintEncodings.find(_constraint);
                if(it != mConstraintEncodings.end())
                {
                    mCurrentEncodings.insert(it->second.begin(), it->second.end());
                    return mConstraintBits[_constraint];
                }
                #endif

                // The constraint has not been encoded yet. Encode it now
                mCurrentConstraint = _constraint;
                carl::BVCompareRelation relation = _constraint.relation();
                Bit out;

                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << "[BV] Encoding constraint: " << _constraint << std::endl;
                #endif

                switch(relation)
                {
                    case carl::BVCompareRelation::EQ:
                        out = encodeEq(lhs, rhs); break;
                    case carl::BVCompareRelation::NEQ:
                        out = encodeNeq(lhs, rhs); break;
                    case carl::BVCompareRelation::ULT:
                        out = encodeUlt(lhs, rhs); break;
                    case carl::BVCompareRelation::ULE:
                        out = encodeUle(lhs, rhs); break;
                    case carl::BVCompareRelation::UGT:
                        out = encodeUgt(lhs, rhs); break;
                    case carl::BVCompareRelation::UGE:
                        out = encodeUge(lhs, rhs); break;
                    case carl::BVCompareRelation::SLT:
                        out = encodeSlt(lhs, rhs); break;
                    case carl::BVCompareRelation::SLE:
                        out = encodeSle(lhs, rhs); break;
                    case carl::BVCompareRelation::SGT:
                        out = encodeSgt(lhs, rhs); break;
                    case carl::BVCompareRelation::SGE:
                        out = encodeSge(lhs, rhs); break;
                    default:
                        assert(false);
                }

                mConstraintBits[_constraint] = out;
                mCurrentConstraint = std::nullopt;

                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << "Encoded into: <" << out << ">" << std::endl;
                #endif

                return out;
            }

            Bit encodeEq(const Bits& _lhs, const Bits& _rhs)
            {
                Bits comparisons;

                for(std::size_t i=0;i<_lhs.size();++i)
                {
                    comparisons.push_back(boolIff(_lhs[i], _rhs[i]));
                }

                return createBit(boolAnd(comparisons));
            }

            Bit encodeNeq(const Bits& _lhs, const Bits& _rhs)
            {
                return createBit(boolNot(encodeEq(_lhs, _rhs)));
            }

            Bit encodeUlt(const Bits& _lhs, const Bits& _rhs)
            {
                return createBit(boolNot(encodeUge(_lhs, _rhs)));
            }

            Bit encodeUle(const Bits& _lhs, const Bits& _rhs)
            {
                Bit ult = encodeUlt(_lhs, _rhs);
                Bit eq = encodeEq(_lhs, _rhs);

                return createBit(boolOr(eq, ult));
            }

            Bit encodeUgt(const Bits& _lhs, const Bits& _rhs)
            {
                return createBit(boolNot(encodeUle(_lhs, _rhs)));
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

                return createBit(boolOr(
                    boolAnd(msbLhs, boolNot(msbRhs)),
                    boolAnd(boolIff(msbLhs, msbRhs), ult)
                ));
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

                return createBit(boolOr(
                    boolAnd(msbLhs, boolNot(msbRhs)),
                    boolAnd(boolIff(msbLhs, msbRhs), ule)
                ));
            }

            Bit encodeSgt(const Bits& _lhs, const Bits& _rhs)
            {
                return createBit(boolNot(encodeSle(_lhs, _rhs)));
            }

            Bit encodeSge(const Bits& _lhs, const Bits& _rhs)
            {
                return createBit(boolNot(encodeSlt(_lhs, _rhs)));
            }

            Bit createBit(const FormulaT& _formula)
            {
                if(_formula.is_atom() || (_formula.type() == carl::FormulaType::NOT && _formula.subformula().is_atom())) {
                    return _formula;
                }

                Bit freshBit = Bit(createVariable());
                boolAssert(boolIff(freshBit, _formula));
                return freshBit;
            }

            Bits createBits(std::size_t _n)
            {
                return createBits(createVariables(_n));
            }

            Variable createVariable()
            {
                Variable var = carl::fresh_boolean_variable();
                #ifndef SMTRAT_BV_ENCODER_DEBUG
                mIntroducedVariables.insert(var);
                #endif
                return var;
            }

            Variables createVariables(std::size_t _n) {
                Variables out;
                for(std::size_t i=0;i<_n;++i) {
                    out.push_back(createVariable());
                }
                return out;
            }

            Bits createBits(const Bits& _original) {
                /*
                 * return _original;
                 */
                Bits out;
                for(const Bit& bit : _original) {
                    out.push_back(createBit(bit));
                }
                return out;
            }

            Bits createBits(const Variables& _variables) {
                Bits out;
                for(const Variable& var : _variables) {
                    out.push_back(Bit(var));
                }
                return out;
            }

            Bit boolNot(const Bit& _operand) {
                return Formula(carl::FormulaType::NOT, _operand);
            }

            Bit boolImplies(const Bit& _first, const Bit& _second) {
                return Formula(carl::FormulaType::IMPLIES, {_first, _second});
            }

            Bit boolAnd(const Bit& _first, const Bit& _second) {
                return Formula(carl::FormulaType::AND, {_first, _second});
            }

            Bit boolAnd(const Bits& _operands) {
                return Formula(carl::FormulaType::AND, _operands);
            }

            Bit boolOr(const Bit& _first, const Bit& _second) {
                return Formula(carl::FormulaType::OR, {_first, _second});
            }

            Bit boolOr(const Bits& _operands) {
                return Formula(carl::FormulaType::OR, _operands);
            }

            Bit boolXor(const Bit& _first, const Bit& _second) {
                return Formula(carl::FormulaType::XOR, {_first, _second});
            }

            Bit boolIff(const Bit& _first, const Bit& _second) {
                return Formula(carl::FormulaType::IFF, {_first, _second});
            }

            Bit boolIte(const Bit& _condition, const Bit& _then, const Bit& _else) {
                return Formula(carl::FormulaType::ITE, {_condition, _then, _else});
            }

            FormulaT encodeBVConstraints(const FormulaT _original)
            {
                if(_original.type() == carl::FormulaType::BITVECTOR)
                {
                    Bit substitute = encodeConstraint(_original.bv_constraint());
                    return substitute;
                }
                return _original;
            }

        public:

            const FormulaSetT& encode(const FormulaT& _inputFormula)
            {
                mCurrentEncodings.clear();
                std::function<FormulaT(FormulaT)> encodeConstraints = std::bind(&BVDirectEncoder::encodeBVConstraints, this, std::placeholders::_1);
                FormulaT passedFormula = carl::visit_result(_inputFormula, encodeConstraints);

                #ifdef SMTRAT_BV_ENCODER_DEBUG
                std::cerr << "Formula encoded into: " << passedFormula << std::endl;
                #endif

                mCurrentEncodings.insert(passedFormula);
                return mCurrentEncodings;
            }

            const std::set<carl::Variable>& introducedVariables() const
            {
                return mIntroducedVariables;
            }

            const carl::FastMap<BitVec, Variables> bitvectorBlastings() const
            {
                return mBitVecBits;
            }

            BVDirectEncoder()
            {
                /* Bits consts = createBits(2);
                mConst0 = consts[0];
                mConst1 = consts[1]; */
            }

            ~BVDirectEncoder()
            {}

    };
}
