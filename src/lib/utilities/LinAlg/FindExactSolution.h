/** 
 * @file   FindExactSolution.h
 * @author: Sebastian Junges
 *
 * 
 */

#ifndef FINDEXACTSOLUTION_H
#define	FINDEXACTSOLUTION_H

#include "DenseMatrix.h"
#include <ginacra/SternBrocot.h>

using GiNaCRA::SternBrocot;
using GiNaCRA::ApproxExact;

namespace smtrat{

	static bool orderAccordingRelError(const std::pair<size_t, GiNaCRA::ApproxExact>& e1, const std::pair<size_t, GiNaCRA::ApproxExact>& e2) {
		return !GiNaCRA::ApproxExact::compareRelError(e1.second, e2.second);
	}
	
	
	class FindExactSolution {
	public:
		FindExactSolution(const std::vector<double>& approxSol, const DenseMatrix& linEq, double precision) : mLinEq(linEq), mApproxSol(approxSol), mPrecision(precision) {
			calculate();
		}
		
		void calculate() {
			SternBrocot sb(mPrecision);
			// We construct (nice) rationals from the doubles
			for(size_t i = 0; i<mApproxSol.size(); ++i) {
				mExactApprox.push_back(std::pair<size_t, GiNaCRA::ApproxExact>(i, sb.rationalize(mApproxSol[i])));
			}
			mExactApprox.sort(orderAccordingRelError);
			std::vector<size_t> colOrder;
			std::vector<Rational> appSol;
			std::transform(mExactApprox.begin(), mExactApprox.end(), std::back_inserter(colOrder), 
					[](const std::pair<size_t, ApproxExact>& p) { return p.first; });
			std::transform(mExactApprox.begin(), mExactApprox.end(), std::back_inserter(appSol),
					[](const std::pair<size_t, ApproxExact>& p) { return p.second.rational; });
			//The last column (the rhs) should stay on the rhs. 
			colOrder.push_back(colOrder.size());
			mLinEq.permuteColumns(colOrder);
			mLinEq.rowEchelon();
			std::vector<Rational> solution(mLinEq.SolveExactSolution(appSol));
			mSolution =  std::vector<Rational>(solution.size());
			
			//We remove the last column as this was the rhs, so it has no corresponding variable
			colOrder.pop_back();
			
			auto jt = solution.begin();
			for(auto it = colOrder.begin(); it != colOrder.end(); ++it) {
				assert(*it < mSolution.size());
				mSolution[*it] = *jt;
				++jt;
			}
		}
		
		DenseMatrix getSolutionMatrix(unsigned size) const{
			return DenseMatrix(size, size, mSolution);
			
		}
		
		DenseMatrix getSolutionMatrix(unsigned height, unsigned width) {
			return DenseMatrix(height, width, mSolution);
		}
		
		double setToHigherPrecision() {
			mPrecision /= 10;
			return mPrecision;
		}
		
		void print(std::ostream& os = std::cout) {
			for(auto it = mExactApprox.begin(); it != mExactApprox.end(); ++it) {
				os << it->first << ", ";
				it->second.print(os); 
				os << std::endl;
			}
		}

		
		virtual ~FindExactSolution() {}
	private:
		DenseMatrix mLinEq;
		std::list<std::pair<size_t, GiNaCRA::ApproxExact> > mExactApprox;
		std::vector<Rational> mSolution;
		const std::vector<double> mApproxSol;
		double mPrecision;
	};
}

#endif	/* FINDEXACTSOLUTION_H */

