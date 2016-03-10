#include "ModelSubstitution.h"

#include "Model.h"

namespace smtrat {
    
        const ModelValue& ModelSubstitution::getModelValue( const ModelVariable& _mvar, Model& _model )
        {
            auto it = _model.find( _mvar );
            assert( it != _model.end() );
            ModelValue& mv = it->second;
            if( mv.isSubstitution() )
            {
                mv = mv.asSubstitution()->evaluate( _model );
            }
            return mv;
        }
        
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
			const ModelValue& mv = getModelValue(ModelVariable(var),model);
			assert( !mv.isSubstitution() );
			if (mv.isRational()) {
				map.emplace(var, carl::RealAlgebraicNumber<Rational>(mv.asRational()));
			} else if (mv.isRAN()) {
				map.emplace(var, mv.asRAN());
			} else {
                            return this;
			}	
		}
                carl::RealAlgebraicNumber<smtrat::Rational> ran = carl::RealAlgebraicNumberEvaluation::evaluate(mPoly, map);
                if( ran.isNumeric() )
                    return ModelValue (ran.value() );
		return ModelValue(ran);
	}
}
