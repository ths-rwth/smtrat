#pragma once

#include <functional>
#include <vector>

#include <carl-arith/poly/umvpoly/functions/IntervalEvaluation.h>

#include "../common.h"
#include "../utils/CADConstraints.h"

#include "PolynomialLiftingQueue.h"
#include "../projectionoperator/ProjectionOperator.h"
#include "ProjectionInformation.h"
#include "Projection_utils.h"

namespace smtrat {
namespace cad {
	
	template<typename Settings>
	class BaseProjection {
	protected:
		using Constraints = CADConstraints<Settings::backtracking>;
	private:
		/// Lift of id pools to generate fresh IDs for polynomials.
		std::vector<carl::IDPool> mIDPools;
		
	protected:
		const Constraints& mConstraints;
		/// List of lifting queues that can be used for incremental projection.
		std::vector<PolynomialLiftingQueue<BaseProjection>> mLiftingQueues;
		/// Additional info on projection, projection levels and projection polynomials.
		ProjectionInformation mInfo;
		/// The projection operator.
		ProjectionOperator mOperator;
		/// Callback to be called when polynomials are removed. The arguments are the projection level and a bitset that indicate which polynomials were removed in this level.
		std::function<void(std::size_t, const SampleLiftedWith&)> mRemoveCallback;
		
		BaseProjection(const Constraints& c): mConstraints(c) {}
		
		void callRemoveCallback(std::size_t level, const SampleLiftedWith& slw) const {
			if (mRemoveCallback) mRemoveCallback(level, slw);
		}
		/// Returns a fresh polynomial id for the given level.
		std::size_t getID(std::size_t level) {
			assert(level <= dim());
			return mIDPools[level].get();
		}
		/// Frees a currently used polynomial id for the given level.
		void freeID(std::size_t level, std::size_t id) {
			assert(level <= dim());
			mIDPools[level].free(id);
		}
		/// Returns the variable that corresponds to the given level, that is the variable eliminated in this level.
		carl::Variable var(std::size_t level) const {
			assert(level > 0 && level <= dim());
			return vars()[level - 1];
		}
		/// Checks whether a polynomial can safely be ignored due to the bounds.
		bool canBePurgedByBounds(const UPoly& p) const {
			if (Settings::simplifyProjectionByBounds) {
				carl::Interval<Rational> res;
				const auto& map = mConstraints.bounds().getEvalIntervalMap();
				if (map.count(p.main_var()) > 0) {
					res = carl::evaluate(p, map);
				} else {
					res = carl::evaluate(Poly(p), map);
				}
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Bounds:" << std::endl << mConstraints.bounds().getEvalIntervalMap());
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Checking polynomial " << p << " against bounds, results in " << res);
				if (res.is_positive() || res.is_negative()) return true;
				SMTRAT_LOG_DEBUG("smtrat.cad.projection", "No.");
			}
			return false;
		}

		bool isPurged(std::size_t level, std::size_t id) {
			if (!mInfo(level).isEvaluated(id)) {
				bool cbp = canBePurgedByBounds(this->getPolynomialById(level, id));
				if (cbp) {
					mInfo(level).setPurged(id, true);
				}
				mInfo(level).setEvaluated(id, true);
			}
			return mInfo(level).isPurged(id);
		}
	public:
		/// Returns the dimension of the projection.
		std::size_t dim() const {
			assert(vars().size() + 1 == mIDPools.size());
			assert(vars().size() == mLiftingQueues.size());
			return vars().size();
		}
		/// Returns the variables used for projection.
		const auto& vars() const {
			return mConstraints.vars();
		}
		/// Resets all datastructures, use the given variables from now on.
		void reset() {
			mIDPools = std::vector<carl::IDPool>(vars().size() + 1);
			mLiftingQueues.clear();
			for (std::size_t i = 1; i <= vars().size(); i++) {
				mLiftingQueues.emplace_back(this, i);
			}
		}
		/// Sets a callback that is called whenever polynomials are removed.
		template<typename F>
		void setRemoveCallback(F&& f) {
			mRemoveCallback = f;
		}
		/// Adds the given polynomial to the projection. Converts to a UPoly and calls the appropriate overload.
		carl::Bitset addPolynomial(const Poly& p, std::size_t cid, bool isBound) {
			return addPolynomial(carl::to_univariate_polynomial(p, var(0)), cid, isBound);
		}
		/// Adds the given polynomial to the projection.
		virtual carl::Bitset addPolynomial(const UPoly& p, std::size_t cid, bool isBound) = 0;
                /// Adds the given polynomial of an equational constraint to the projection. Converts to a UPoly and calls the appropriate overload.
		carl::Bitset addEqConstraint(const Poly& p, std::size_t cid, bool isBound) {
			return addEqConstraint(carl::to_univariate_polynomial(p, var(0)), cid, isBound);
		}
		/// Adds the given polynomial of an equational constraint to the projection.
		virtual carl::Bitset addEqConstraint(const UPoly& p, std::size_t cid, bool isBound) {
                        return addPolynomial(p, cid, isBound);
                }
		/// Removes the given polynomial from the projection. Converts to a UPoly and calls the appropriate overload.
		void removePolynomial(const Poly& p, std::size_t cid, bool isBound) {
			removePolynomial(carl::to_univariate_polynomial(p, var(0)), cid, isBound);
		}
		/// Removes the given polynomial from the projection.
		virtual void removePolynomial(const UPoly& p, std::size_t cid, bool isBound) = 0;
		
		virtual std::size_t size(std::size_t level) const = 0;
		std::size_t size() const {
			std::size_t sum = 0;
			for (std::size_t level = 1; level <= dim(); level++) {
				sum += size(level);
			}
			return sum;
		}
		virtual bool empty(std::size_t level) const = 0;
		virtual bool empty() {
			for (std::size_t level = 1; level <= dim(); level++) {
				if (!empty(level)) return false;
			}
			return true;
		}
		
		/// Get a polynomial from this level suited for lifting.
		OptionalID getPolyForLifting(std::size_t level, SampleLiftedWith& slw) {
			assert(level > 0);
			assert(level <= dim());
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "Getting poly for lifting from level " << level);
			for (const auto& pid: mLiftingQueues[level - 1]) {
				SMTRAT_LOG_TRACE("smtrat.cad.projection", "-> Checking " << getPolynomialById(level,pid));
				if (!slw.test(pid)) {
					SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> " << getPolynomialById(level,pid) << " can be used.");
					slw.set(pid);
					return OptionalID(pid);
				}
			}
			SMTRAT_LOG_DEBUG("smtrat.cad.projection", "-> None.");
			return OptionalID();
		}
		
		virtual bool hasPolynomialById(std::size_t level, std::size_t id) const = 0;
		/// Retrieves a polynomial from its id.
		virtual const UPoly& getPolynomialById(std::size_t level, std::size_t id) const = 0;
		
		virtual void exportAsDot(std::ostream&) const {}
		virtual Origin getOrigin(std::size_t level, std::size_t id) const {
			if (mInfo.hasInfo(level, id)) return mInfo(level, id).origin;
			return Origin();
		}
	};
	
}
}
