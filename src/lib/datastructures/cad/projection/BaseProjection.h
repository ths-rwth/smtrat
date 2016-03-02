#pragma once

#include <vector>

#include "../Common.h"
#include "../utils/IDPool.h"

#include "ProjectionOperator.h"
#include "PolynomialLiftingQueue.h"

namespace smtrat {
namespace cad {
	
	class BaseProjection {
	public:
		using PolynomialSelection = Bitset;
		using ConstraintSelection = Bitset;
	protected:
		Variables mVariables;
		std::vector<IDPool> mIDPools;
		std::vector<PolynomialLiftingQueue<BaseProjection>> mLiftingQueues;
		ProjectionOperator mOperator;
		
		std::size_t dim() const {
			assert(mVariables.size() == mIDPools.size());
			assert(mVariables.size() == mLiftingQueues.size());
			return mVariables.size();
		}
		std::size_t getID(std::size_t level) {
			assert(level < dim());
			return mIDPools[level].get();
		}
		void freeID(std::size_t level, std::size_t id) {
			assert(level < dim());
			mIDPools[level].free(id);
		}
		carl::Variable var(std::size_t level) const {
			assert(level < dim());
			return mVariables[level];
		}
	public:
		const Variables& vars() const {
			return mVariables;
		}
		void reset(const Variables& vars) {
			mVariables = vars;
			mIDPools = std::vector<IDPool>(vars.size());
			mLiftingQueues.clear();
			for (std::size_t i = 0; i < vars.size(); i++) {
				mLiftingQueues.emplace_back(this, i);
			}
		}
		void addPolynomial(const Poly& p) {
			addPolynomial(p.toUnivariatePolynomial(var(0)));
		}
		virtual void addPolynomial(const UPoly& p) = 0;
		void removePolynomial(const Poly& p) {
			removePolynomial(p.toUnivariatePolynomial(var(0)));
		}
		virtual void removePolynomial(const UPoly& p) = 0;
		
		void cleanLiftedWith(std::size_t level, SampleLiftedWith& slw) const {
			mIDPools[level].purgeUnusedIDs(slw);
		}
		
		virtual const UPoly& getPolynomialById(std::size_t level, std::size_t id) const = 0;
	};
	
}
}
