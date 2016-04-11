#include "ModelSubstitution.h"

#include "Model.h"

namespace smtrat {
        
        void ModelPolynomialSubstitution::multiplyBy( const Rational& _number )
        {
            mPoly *= _number;
        }
        
        void ModelPolynomialSubstitution::add( const Rational& _number )
        {
            mPoly += _number;
        }
    
	ModelValue ModelPolynomialSubstitution::evaluate(Model& model) {
		carl::RealAlgebraicNumberEvaluation::RANMap<Rational> map;
		for (const auto& var: mVars) {
			auto it = model.find(ModelVariable(var));
			if (it == model.end()) {
				return Poly(var);
			}
			const ModelValue& mv = getModelValue(it,model);
			assert( !mv.isSubstitution() );
			if (mv.isRational()) {
				SMTRAT_LOG_WARN("smtrat.model", "Substituting " << var << " = " << mv.asRational() << " into " << mPoly);
				mPoly.substituteIn(var, Poly(mv.asRational()));
				SMTRAT_LOG_WARN("smtrat.model", "-> " << mPoly);
			} else if (mv.isRAN()) {
				SMTRAT_LOG_WARN("smtrat.model", "Substituting " << var << " = " << mv.asRAN() << " into " << mPoly);
				map.emplace(var, mv.asRAN());
			} else if (mv.isPoly()) {
				SMTRAT_LOG_WARN("smtrat.model", "Substituting " << var << " = " << mv.asPoly() << " into " << mPoly);
				mPoly.substituteIn(var, mv.asPoly());
				SMTRAT_LOG_WARN("smtrat.model", "-> " << mPoly);
			} else {
                            return this;
			}	
		}
		if (map.size() > 0) {
                carl::RealAlgebraicNumber<smtrat::Rational> ran = carl::RealAlgebraicNumberEvaluation::evaluate(mPoly, map);
                if( ran.isNumeric() )
                    return ModelValue (ran.value() );
					return ModelValue(ran);
				}
		return mPoly;
	}
}
