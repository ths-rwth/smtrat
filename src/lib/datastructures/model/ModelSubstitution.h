#pragma once

#include <iostream>
#include <map>
#include <memory>

#include <carl/core/RealAlgebraicNumberEvaluation.h>
#include "../../Common.h"
#include "ModelValue.h"
#include "ModelVariable.h"

namespace smtrat {
	class Model;
	class ModelSubstitution {
	protected:
	public:
		ModelSubstitution() {}
		virtual ~ModelSubstitution() {}
		
		/// Evaluates this substitution with respect to the given model.
		virtual ModelValue evaluate(Model& model) = 0;
		/// Checks whether this substitution needs the given model variable.
		virtual bool dependsOn(const ModelVariable&) const {
			return true;
		}
		/// Prints this substitution to the given output stream.
		virtual void print(std::ostream& os) const {
			os << "substitution";
		}
		/// Multiplies this model substitution by a rational.
		virtual void multiplyBy( const Rational& _number ) = 0;
		/// Adds a rational to this model substitution.
		virtual void add( const Rational& _number ) = 0;
        
        const ModelValue& getModelValue( const ModelVariable& _mvar, Model& _model );
		
		template<typename Substitution, typename... Args>
		static ModelValue create(Args&&... args) {
			return ModelValue(std::make_shared<Substitution>(std::forward<Args>(args)...));
		}
	};
	inline std::ostream& operator<<(std::ostream& os, const ModelSubstitution& ms) {
		ms.print(os);
		return os;
	}
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
		virtual void multiplyBy( const Rational& _number );
		virtual void add( const Rational& _number );
		virtual ModelValue evaluate(Model& model);
		virtual bool dependsOn(const ModelVariable& var) const {
			if (!var.isVariable()) return false;
			return mPoly.degree(var.asVariable()) > 0;
		}
		virtual void print(std::ostream& os) const {
			os << mPoly;
		}
	};
	
}
