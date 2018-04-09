/**
 * @file PBPP.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-11-23
 * Created on 2016-11-23.
 */

#include "PBPPModule.h"

#include "RNSEncoder.h"

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
            // const Poly& lhs = constraint.lhs();
            // const Rational rhs = constraint.constantPart();
            // const carl::Relation relation = constraint.relation();

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
            // It could take into account:
            // - number of newly created constraints
            // - number of eliminated variables (could be expensive)
            // --- relative size propositional constraint/arithmetic constraint
            // --- relative size considering the whole formula

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
            // However, we can still have LEQ, LESS, EQUAL, NEQ
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
                // not only positive and not only negative -> has both, positive and negative coeff
                auto res = encodeMixedConstraints(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else if(isAllCoeffEqual && (lhs.lcoeff() == 1 || lhs.lcoeff() == -1 ) && lhsSize > 1){
                // x1 + x2 - x3 ~ b
                auto res = encodeCardinalityConstraint(constraint);
                SMTRAT_LOG_INFO("smtrat.pbc", inputFormula << " -> " << res);
                return res;
            }else if((lhsSize == 1 && !lhs.begin()->isConstant()) || lhsSize == 2){
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

            RNSEncoder encoder;
            // TODO we want to further distinguish whether we need 4 or 5 since we might have a constant term
            if(positive && !(isAllCoeffEqual && cLHS.lcoeff() == 1) && cRel == carl::Relation::EQ && cLHS.size() > 4){
                boost::optional<FormulaT> encodedFormula = encoder.encode(constraint);
                if (encodedFormula) {
                    return *encodedFormula;
                }
            }

            return checkFormulaType(formula);
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
        FormulaT PBPPModule<Settings>::encodeMixedConstraints(const ConstraintT& constraint){
            return encodeConstraintOrForwardAsArithmetic(constraint, mMixedSignEncoder);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::encodeCardinalityConstraint(const ConstraintT& constraint){
            return encodeConstraintOrForwardAsArithmetic(constraint, mCardinalityEncoder);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::convertSmallFormula(const ConstraintT& constraint){
            return encodeConstraintOrForwardAsArithmetic(constraint, mShortFormulaEncoder);
        }

    template<typename Settings>
        FormulaT PBPPModule<Settings>::convertBigFormula(const ConstraintT& constraint){
            return encodeConstraintOrForwardAsArithmetic(constraint, mLongFormulaEncoder);
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
        FormulaT PBPPModule<Settings>::encodeConstraintOrForwardAsArithmetic(const ConstraintT& constraint, PseudoBoolEncoder& encoder) {
            boost::optional<FormulaT> encodedFormula = encoder.encode(constraint);
            if (encodedFormula) {
                return *encodedFormula;
            }

            return forwardAsArithmetic(constraint);
        }
}

#include "Instantiation.h"
