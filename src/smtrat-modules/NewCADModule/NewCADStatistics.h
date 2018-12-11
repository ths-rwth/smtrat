/**
 * @file NewCADStatistics.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2016-02-23
 * Created on 2016-02-23.
 */

#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <lib/utilities/stats/Statistics.h>

namespace smtrat
{
	class NewCADStatistics : public Statistics {
	private:
		size_t mUsedCAD = 0;
		bool mECInCAD = false;
		std::size_t mComputedPolynomials = 0;
		std::size_t mUsedRestrictedProj = 0;

		std::size_t mMaxPurgedPolynomials = 0;

		std::size_t mMaxProjectionSize = 0;
	public:
		void collect()
		{
		   Statistics::addKeyValuePair("used_cad", mUsedCAD);
		   Statistics::addKeyValuePair("ec_in_cad", mECInCAD);
		   Statistics::addKeyValuePair("computed_polynomials", mComputedPolynomials);
		   Statistics::addKeyValuePair("used_restricted_projection", mUsedRestrictedProj);
		   Statistics::addKeyValuePair("max_purged_polynomials", mMaxPurgedPolynomials);
		   Statistics::addKeyValuePair("max_projection_size", mMaxProjectionSize);
		}
		void usedCAD() {
			mUsedCAD += 1;
		}
		void addedECtoCAD() {
			mECInCAD = true;
		}
		void computePolynomial() {
			mComputedPolynomials += 1;
		}
		void usedRestrictedProjection() {
			mUsedRestrictedProj += 1;
		}
		void currentlyPurgedPolynomials(std::size_t number) {
			mMaxPurgedPolynomials = std::max(mMaxPurgedPolynomials, number);
		}
		void currentProjectionSize(std::size_t size) {
			mMaxProjectionSize = std::max(mMaxProjectionSize, size);
		}
		NewCADStatistics( const std::string& _statisticName ):
			Statistics( _statisticName, this )
		{}
		~NewCADStatistics() {}
	};
}

#endif
