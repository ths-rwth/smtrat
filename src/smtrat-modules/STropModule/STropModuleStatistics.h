#pragma once

#include <smtrat-common/smtrat-common.h>
#ifdef SMTRAT_DEVOPTION_Statistics
#include <smtrat-common/statistics/Statistics.h>
namespace smtrat{
    class STropModuleStatistics : public Statistics{
        public:
            enum class AnswerBy {NOMEANING = 0, TRIVIALUNSAT = 1, THEORYSOLVED = 2, BACKEND = 3, PARSER = 4};
        private:
            AnswerBy mAnswerBy = AnswerBy::NOMEANING;
            carl::statistics::timer mTheoryTimer;
            carl::statistics::timer mTransformationTimer;
        public:
            void collect(){
                Statistics::addKeyValuePair("Answered_by", (int)mAnswerBy);
                Statistics::addKeyValuePair("Theory_Time_[ms]", mTheoryTimer);
                Statistics::addKeyValuePair("Transformation_Time_[ms]", mTransformationTimer);
            }

            void setAnswerBy(AnswerBy answerBy){
                mAnswerBy = answerBy;
            }

            auto& theoryTimer(){
                return mTheoryTimer;
            }

            auto& transformationTimer(){
                return mTransformationTimer;
            }
    };
}
#endif