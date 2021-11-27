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
	// counts the number of "resultant-barriers" created in the third (smart Heuristic)
	std::size_t mResultantBarriersH3 = 0;
	// the maximal degree a polynomial has during calculations
	std::size_t mMaxDegree = 0;
    // number of traversed levels during Onecell cad
    std::size_t mLevels = 0;
    // number of zeros encountered during onecell cad
    std::size_t mZeros = 0;
    // number of resultants encountered during onecell cad
    std::size_t mResultants = 0;
    // saves the number of traversed levels which did not have any roots
    std::size_t mLevelsWOzeros = 0;
    // saves the number of traversed levels which did not have any polynomials
    std::size_t mLevelsWOpols = 0;
public:
	bool enabled() const {
		return true;
	}

	void collect() {
		Statistics::addKeyValuePair("explanation_called", mExplanationCalled);
		Statistics::addKeyValuePair("explanation_success", mExplanationSuccess);
        Statistics::addKeyValuePair("resultant_barriers", mResultantBarriersH3);
        Statistics::addKeyValuePair("max_degree", mMaxDegree);
        Statistics::addKeyValuePair("num_of_levels", mLevels);
        Statistics::addKeyValuePair("num_of_zeros", mZeros);
        Statistics::addKeyValuePair("num_of_resultants", mResultants);
        Statistics::addKeyValuePair("num_of_levels_wo_zeros", mLevelsWOzeros);
        Statistics::addKeyValuePair("num_of_levels_wo_pols", mLevelsWOpols);
	}

	void explanationCalled() {
		++mExplanationCalled;
	}

	void explanationSuccess() {
		++mExplanationSuccess;
	}

	void resultantBarrierCreated(){
	    ++mResultantBarriersH3;
	}

    void addLevels(std::size_t l){
        mLevels += l;
    }

	// To disable this statistics, set variable in appendOnCorrectLevel() in utils.h
	void updateMaxDegree(std::size_t NewDeg){
	    mMaxDegree = NewDeg;
	}

	std::size_t getCurrentMaxDegree(){
	    return mMaxDegree;
	}

    void addZeros(std::size_t z){
        mZeros += z;
    }

    void addResultants(std::size_t r){
        mResultants += r;
    }

    void levelWOzeros(){
        ++mLevelsWOzeros;
    }

    void levelWOpols(){
        ++mLevelsWOpols;
    }
};

}
}
}

#endif
