#pragma once

#include <smtrat-common/statistics/Statistics.h>

#ifdef SMTRAT_DEVOPTION_Statistics

namespace smtrat {
namespace mcsat {
namespace onecellcad {

class OCStatistics : public Statistics {
private:
	std::size_t mExplanationCalled = 0;
	std::size_t mExplanationSuccess = 0;

	// counts the number of "resultant-barriers"
	std::size_t mResultantBarriers = 0;
    std::size_t mResultantBarriersTotal = 0;
    std::size_t mResultantBarriersTemp = 0;
	// the maximal degree a polynomial has during calculations
	std::size_t mMaxDegree = 0;
    std::size_t mMaxDegreeTotal = 0;
    std::size_t mMaxDegreeTemp = 0;
    // number of traversed levels during Onecell cad
    std::size_t mLevels = 0;
    std::size_t mLevelsTotal = 0;
    std::size_t mLevelsTemp = 0;
    // number of zeros encountered during onecell cad
    std::size_t mZeros = 0;
    std::size_t mZerosTotal = 0;
    std::size_t mZerosTemp = 0;
    // number of resultants encountered during onecell cad
    std::size_t mResultants = 0;
    std::size_t mResultantsTotal = 0;
    std::size_t mResultantsTemp = 0;
    // number of discriminants encountered during onecell cad
    std::size_t mDiscriminants = 0;
    std::size_t mDiscriminantsTotal = 0;
    std::size_t mDiscriminantsTemp = 0;
    // number of coefficients encountered during onecell cad
    std::size_t mCoefficients = 0;
    std::size_t mCoefficientsTotal = 0;
    std::size_t mCoefficientsTemp = 0;
    // saves the number of traversed levels which did not have any roots
    std::size_t mLevelsWOzeros = 0;
    std::size_t mLevelsWOzerosTotal = 0;
    std::size_t mLevelsWOzerosTemp = 0;
    // saves the number of traversed levels which did not have any polynomials
    std::size_t mLevelsWOpols = 0;
    std::size_t mLevelsWOpolsTotal = 0;
    std::size_t mLevelsWOpolsTemp = 0;


public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);

        Statistics::addKeyValuePair("resultant_barriers", mResultantBarriers);
        Statistics::addKeyValuePair("max_degree", mMaxDegree);
        Statistics::addKeyValuePair("num_of_levels", mLevels);
        Statistics::addKeyValuePair("num_of_zeros", mZeros);
        Statistics::addKeyValuePair("num_of_resultants", mResultants);
        Statistics::addKeyValuePair("num_of_discriminants", mDiscriminants);
        Statistics::addKeyValuePair("num_of_coefficients", mCoefficients);
        Statistics::addKeyValuePair("num_of_levels_wo_zeros", mLevelsWOzeros);
        Statistics::addKeyValuePair("num_of_levels_wo_pols", mLevelsWOpols);

        Statistics::addKeyValuePair("resultant_barriers_total", mResultantBarriersTotal);
        Statistics::addKeyValuePair("max_degree_total", mMaxDegreeTotal);
        Statistics::addKeyValuePair("num_of_levels_total", mLevelsTotal);
        Statistics::addKeyValuePair("num_of_zeros_total", mZerosTotal);
        Statistics::addKeyValuePair("num_of_resultants_total", mResultantsTotal);
        Statistics::addKeyValuePair("num_of_discriminants_total", mDiscriminantsTotal);
        Statistics::addKeyValuePair("num_of_coefficients_total", mCoefficientsTotal);
        Statistics::addKeyValuePair("num_of_levels_wo_zeros_total", mLevelsWOzerosTotal);
        Statistics::addKeyValuePair("num_of_levels_wo_pols_total", mLevelsWOpolsTotal);
	}

	void explanationCalled() {
		++mExplanationCalled;
        mResultantBarriersTemp = 0;
        mMaxDegreeTemp = 0;
        mLevelsTemp = 0;
        mZerosTemp = 0;
        mResultantsTemp = 0;
        mDiscriminantsTemp = 0;
        mCoefficientsTemp = 0;
        mLevelsWOzerosTemp = 0;
        mLevelsWOpolsTemp = 0;
	}

	void explanationSuccess() {
		++mExplanationSuccess;

        mResultantBarriers += mResultantBarriersTemp;
        mMaxDegree = std::max(mMaxDegreeTemp,mMaxDegree);
        mLevels += mLevelsTemp;
        mZeros += mZerosTemp;
        mResultants += mResultantsTemp;
        mDiscriminants += mDiscriminantsTemp;
        mCoefficients += mCoefficientsTemp;
        mLevelsWOzeros += mLevelsWOzerosTemp;
        mLevelsWOpols += mLevelsWOpolsTemp;
        // TODO
	}

	void resultantBarrierCreated(){
	    ++mResultantBarriersTotal;
        ++mResultantBarriersTemp;
	}

    void addLevels(std::size_t l){
        mLevels += l;
        mLevelsTemp += l;
    }

	// To disable this statistics, set variable in appendOnCorrectLevel() in utils.h
	void updateMaxDegree(std::size_t NewDeg){
        mMaxDegree = std::max(NewDeg,mMaxDegree);
	    mMaxDegreeTemp = std::max(NewDeg,mMaxDegreeTemp);
	}

    void addZeros(std::size_t z){
        mZeros += z;
        mZerosTemp += z;
    }

    void addResultants(std::size_t r){
        mResultants += r;
        mResultantsTemp += r;
    }

    void addDiscriminants(std::size_t r){
        mDiscriminants += r;
        mDiscriminantsTemp += r;
    }

    void addCoefficients(std::size_t r){
        mCoefficients += r;
        mCoefficientsTemp += r;
    }

    void levelWOzeros(){
        ++mLevelsWOzeros;
        ++mLevelsWOzerosTemp;
    }

    void levelWOpols(){
        ++mLevelsWOpols;
        ++mLevelsWOpolsTemp;
    }
};

}
}
}

#endif
