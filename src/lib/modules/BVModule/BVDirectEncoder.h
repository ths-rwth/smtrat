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

#include "boost/optional/optional.hpp"
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
            // Set of all bits that have been introduced by the encoder
            std::set<Bit> mIntroducedBits;

            // Substituted fresh variables
            //  - for bitvector variables (one variable for each bitvector bit)
            std::map<BitVec, Bits> mBitVecBits;
            //  - for bitvector terms (likewise, one variable for each bitvector bit)
            std::map<BitVecTerm, Bits> mTermBits;
            //  - for bitvector constraints (a single variable)
            std::map<BitVecConstr, Bit> mConstraintBits;

            // Created formulas ("encodings")
            //  - for terms
            std::map<BitVecTerm, FormulasT> mTermEncodings;
            //  - for constraints (not including the encodings for the contained terms)
            std::map<BitVecConstr, FormulasT> mConstraintEncodings;
            //  - for terms and constraints originating from the current input formula
            FormulasT mCurrentEncodings;

            // Encoding state (remember currently encoded constraint/term)
            boost::optional<BitVecConstr> mCurrentConstraint;
            boost::optional<BitVecTerm> mCurrentTerm;

            Bit mConst0;
            Bit mConst1;

            const Bit const0()
            {
                addEncoding(Formula(carl::FormulaType::NOT, Formula(mConst0)));
                return mConst0;
            }

            const Bit const1()
            {
                addEncoding(Formula(mConst1));
                return mConst1;
            }

            void addEncoding(const Formula& _formula)
            {
                if(mCurrentTerm) {
                    mTermEncodings.insert(std::make_pair(*mCurrentTerm, FormulasT()));
                    mTermEncodings[*mCurrentTerm].push_back(_formula);
                } else if(mCurrentConstraint) {
                    mConstraintEncodings.insert(std::make_pair(*mCurrentConstraint, FormulasT()));
                    mConstraintEncodings[*mCurrentConstraint].push_back(_formula);
                }

                mCurrentEncodings.push_back(_formula);
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
                std::map<BitVec, Bits>::iterator it = mBitVecBits.find(_variable);

                if(it == mBitVecBits.end())
                {
                    Bits out = createBits(_variable.width());
                    mBitVecBits[_variable] = out;
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
                    addEncoding(Formula(carl::FormulaType::IFF,
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
                    addEncoding(Formula(carl::FormulaType::XOR,
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
                    addEncoding(Formula(carl::FormulaType::IFF,
                                        Formula(carry[i]),
                                        Formula(carl::FormulaType::AND,
                                                Formula(carry[i-1]),
                                                Formula(negated[i-1]))));
                }

                Bits out = createBits(_operand.size());

                for(size_t i=0;i<_operand.size();++i)
                {
                    addEncoding(Formula(carl::FormulaType::IFF,
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
                    addEncoding(
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

            Bits encodeAdderNetwork(const Bits& _first, const Bits& _second, bool _carryInValue = false, bool _withCarryOut = false, bool _allowOverflow = true)
            {
                Bits out = createBits(_first.size());
                Bits carry = createBits(_first.size() - (_withCarryOut ? 0 : 1));

                carry.insert(carry.begin(), (_carryInValue ? const1() : const0()));
                for(std::size_t i=1;i<carry.size();++i) {
                    addEncoding(Formula(carl::FormulaType::IFF,
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
                    addEncoding(Formula(carl::FormulaType::IFF,
                                        Formula(out[i]),
                                        Formula(carl::FormulaType::XOR,
                                                Formula(_first[i]),
                                                Formula(carl::FormulaType::XOR,
                                                        Formula(_second[i]),
                                                        Formula(carry[i])))));
                }

                if(! _allowOverflow) {
                    addEncoding(Formula(carl::FormulaType::NOT, Formula(carry[carry.size()-1])));
                }
                if(_withCarryOut) {
                    out.insert(out.end(), carry[carry.size()-1]);
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
                    summands[i] = createBits(_first.size() - i);

                    for(std::size_t j=0;j<summands[i].size();++j) {
                        addEncoding(Formula(carl::FormulaType::IFF,
                                            Formula(summands[i][j]),
                                            Formula(carl::FormulaType::ITE,
                                                    Formula(_second[i]),
                                                    Formula(_first[j]),
                                                    Formula(carl::FormulaType::FALSE))));
                    }

                    if(! _allowOverflow) {
                        for(std::size_t j=summands[i].size();j<_first.size();++j) {
                            addEncoding(Formula(carl::FormulaType::OR,
                                                Formula(carl::FormulaType::NOT, Formula(_second[i])),
                                                Formula(carl::FormulaType::NOT, Formula(_first[j]))));
                        }
                    }

                    summands[i].insert(summands[i].begin(), i, const0());
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
                Bits out = createBits(_first.size());
                Bits remainder = createBits(_first.size());

                Bit wellDefined = encodeNeq(_second, encodeConstant(carl::BVValue(_second.size(), 0)));

                Bit summationCorrect = encodeEq(
                    _first,
                    encodeAdderNetwork(
                        encodeMultiplicationNetwork(out, _second, false),
                        remainder,
                        false,
                        false,
                        false
                    )
                );

                Bit remainderLessThanDivisor = encodeUlt(remainder, _second);

                addEncoding(Formula(carl::FormulaType::IMPLIES,
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
                            shifted = _arithmetic ? _first[_first.size() - 1] : const0();
                        }

                        addEncoding(Formula(carl::FormulaType::IFF,
                                            Formula(currentStage[pos]),
                                            Formula(carl::FormulaType::ITE,
                                                    Formula(_second[stage]),
                                                    Formula(shifted),
                                                    Formula(notShifted))));
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
                    Bits out = createBits(_first.size());

                    std::vector<Formula> subFormulas;
                    for(std::size_t pos=highestRelevantPos+1;pos<_second.size();++pos)
                    {
                        subFormulas.push_back(Formula(_second[pos]));
                    }

                    Bit shiftOut = createBit();
                    addEncoding(Formula(carl::FormulaType::IFF,
                                        Formula(shiftOut),
                                        Formula(carl::FormulaType::OR, subFormulas)));

                    for(std::size_t i=0;i<out.size();++i)
                    {
                        addEncoding(Formula(carl::FormulaType::IFF,
                                            Formula(out[i]),
                                            Formula(carl::FormulaType::ITE,
                                                    Formula(shiftOut),
                                                    Formula(_arithmetic ? _first[_first.size()-1] : const0()),
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
                                (_operand.size() -
                                    (_index % _operand.size()))
                                % _operand.size()),
                            out.end());
                return out;
            }

            Bits encodeRrotate(const Bits& _operand, std::size_t _index)
            {
                Bits out(_operand);
                std::rotate(out.begin(),
                            out.begin() + (Bits::difference_type)(
                                _index % _operand.size()),
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

                auto it = mTermEncodings.find(_term);
                if(it != mTermEncodings.end())
                {
                    mCurrentEncodings.insert(mCurrentEncodings.end(), it->second.begin(), it->second.end());
                    return mTermBits[_term];
                }

                // The term has not been encoded yet. Encode it now
                mCurrentTerm = _term;
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
                mCurrentTerm = boost::none;

                return out;
            }

            Bit encodeConstraint(const BitVecConstr& _constraint)
            {
                // Always call encodeTerm() on both subterms, even if we have
                // already encoded _constraint. This way the mCurrentEncodings
                // set is built correctly.
                Bits lhs = encodeTerm(_constraint.lhs());
                Bits rhs = encodeTerm(_constraint.rhs());

                auto it = mConstraintEncodings.find(_constraint);
                if(it != mConstraintEncodings.end())
                {
                    mCurrentEncodings.insert(mCurrentEncodings.end(), it->second.begin(), it->second.end());
                    return mConstraintBits[_constraint];
                }

                // The constraint has not been encoded yet. Encode it now
                mCurrentConstraint = _constraint;
                carl::BVCompareRelation relation = _constraint.relation();
                Bit out;

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
                mCurrentConstraint = boost::none;
                return out;
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

                addEncoding(Formula(carl::FormulaType::IFF,
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
                addEncoding(Formula(carl::FormulaType::IFF,
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

                addEncoding(Formula(carl::FormulaType::IFF,
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

                addEncoding(Formula(carl::FormulaType::IFF,
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
                addEncoding(Formula(carl::FormulaType::XOR, Formula(_original), Formula(out)));
                return out;
            }

            Bit createBit()
            {
                Bit bit = carl::VariablePool::getInstance().getFreshVariable(carl::VariableType::VT_BOOL);
                mIntroducedBits.insert(bit);
                return bit;
            }

            Bits createBits(std::size_t _n)
            {
                Bits out(_n);

                for(std::size_t i=0;i<_n;++i) {
                    out[i] = createBit();
                }

                return out;
            }

            FormulaT encodeBVConstraints(const FormulaT _original)
            {
                if(_original.getType() == carl::FormulaType::BITVECTOR)
                {
                    Bit substitute = encodeConstraint(_original.bvConstraint());
                    return Formula(substitute);
                }
                return _original;
            }

        public:

            const FormulasT& encode(const FormulaT& _inputFormula)
            {
                mCurrentEncodings.clear();
                carl::FormulaVisitor<FormulaT> visitor;
                std::function<FormulaT(FormulaT)> encodeConstraints = std::bind(&BVDirectEncoder::encodeBVConstraints, this, std::placeholders::_1);
                FormulaT passedFormula = visitor.visit(_inputFormula, encodeConstraints);
                mCurrentEncodings.push_back(passedFormula);
                return mCurrentEncodings;
            }

            const std::set<Bit>& introducedBits() const
            {
                return mIntroducedBits;
            }

            const std::map<BitVec, Bits> bitvectorBlastings() const
            {
                return mBitVecBits;
            }

            BVDirectEncoder()
            {
                mConst0 = createBit();
                mConst1 = createBit();
            }

            ~BVDirectEncoder()
            {}

    };
}
