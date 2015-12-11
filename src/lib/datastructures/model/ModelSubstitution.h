#pragma once

#include <iostream>
#include <memory>

#include <carl/core/RealAlgebraicNumberEvaluation.h>
#include "../../Common.h"
#include "Model.h"

namespace smtrat {
	
	class Model;
	class ModelValue;
	
	class ModelSubstitution {
	protected:
	public:
		ModelSubstitution() {}
		virtual ~ModelSubstitution() {}
		
		virtual ModelValue evaluate(Model& model) = 0;
		
		template<typename Substitution, typename... Args>
		static ModelValue create(Args&&... args) {
			return ModelValue(std::make_shared<Substitution>(std::forward<Args>(args)...));
		}
		virtual void print(std::ostream& os) const {
			os << "substitution";
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const std::shared_ptr<ModelSubstitution>& ms) {
		ms->print(os);
		return os;
	}
	
	class ModelPolynomialSubstitution: public ModelSubstitution {
	private:
		Poly mPoly;
		std::set<carl::Variable> mVars;
	public:
		ModelPolynomialSubstitution(const Poly& p): ModelSubstitution(), mPoly(p), mVars(p.gatherVariables())
		{}
		virtual ModelValue evaluate(Model& model) {
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
		virtual void print(std::ostream& os) const {
			os << mPoly;
			if (mValue != nullptr) os << " = " << *mValue;
		}
	};
	
}
