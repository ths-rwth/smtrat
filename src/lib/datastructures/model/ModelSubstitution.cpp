#include "ModelSubstitution.h"

#include "Model.h"

namespace smtrat {
	ModelValue ModelPolynomialSubstitution::evaluate(Model& model) {
		carl::RealAlgebraicNumberEvaluation::RANMap<Rational> map;
		for (const auto& var: mVars) {
			auto it = model.find(ModelVariable(var));
			assert(it != model.end());
			const ModelValue& mv = it->second;
			
			if (mv.isRational()) {
				map.emplace(var, carl::RealAlgebraicNumber<Rational>(mv.asRational()));
			} else if (mv.isRAN()) {
				map.emplace(var, mv.asRAN());
			} else {
				assert(false);
			}	
		}
		return ModelValue(carl::RealAlgebraicNumberEvaluation::evaluate(mPoly, map));
	}
}
