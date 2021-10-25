#pragma once

#include <thread>
#include <unistd.h>

#include "../utils/Bookkeeping.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

/**
 * This explanation executes all given explanation parallel in multiple threads and waits until every single one has finished,
 * returning the result of the first listed explanation
 */
 // TODO currently trying to be FastParallelExplanation, change behavior to description
template<typename... Backends>
struct FullParallelExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;

    template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
    std::optional<Explanation> explain(const mcsat::Bookkeeping&, carl::Variable, const FormulasT&,
                 const std::size_t NUM_THREADS, std::mutex& mtx,
                 std::vector<std::thread>& threads, std::vector<pthread_t>& nativeHandles,
                 size_t& counter, std::vector<std::optional<Explanation>>& explanations) const {

        SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "All explanations started.");
        mtx.unlock();
        void *res;
        int s;
        std::optional<Explanation> explanation;
        while(true) {
            if(counter == NUM_THREADS){ SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "No explanation left."); }
            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Look for resulting explanation");
            for (size_t i = 0; i < NUM_THREADS; i++) {
                explanation = explanations[i];
                if (explanation != std::nullopt) {
                    mtx.lock();
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Found explanation: " << *explanation);
                    for(size_t j = 0; j < NUM_THREADS; j++){
                        pthread_cancel(nativeHandles[j]);

                        s = pthread_join(nativeHandles[j], &res);
                        if(s != 0){ SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "Join failed"); }
                        if (res != PTHREAD_CANCELED){
                            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "Thread not cancelled");
                        } else {
                            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Thread cancelled successfully");
                        }
                    }
                    nativeHandles.clear();
                    mtx.unlock();
                    SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Return reachable");
                    return explanation;
                }
            }
        }

    }

    template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
    std::optional<Explanation> explain(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason,
                 const std::size_t NUM_THREADS, std::mutex& mtx,
                 std::vector<std::thread>& threads, std::vector<pthread_t>& nativeHandles,
                 size_t& counter, std::vector<std::optional<Explanation>>& explanations) const {

        auto F = [&](){
            if(pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL)){
                SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "Pthread set cancel type error");
                assert(false);
            }

            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Concurrent strategy " << N+1 << " started");
            explanations[N] = std::get<N>(mBackends)(data, var, reason);
            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Concurrent strategy " << N+1 << " done");

            mtx.lock();
            counter++;
            mtx.unlock();

            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Concurrent strategy " << N+1 << " waiting");
            //TODO make this a wait()
            while(true){
                //no-op
                (void)0;
            };
        };
        SMTRAT_LOG_TRACE("smtrat.mcsat.explanation", "Create Thread");
        threads.push_back(std::thread(F));
        SMTRAT_LOG_TRACE("smtrat.mcsat.explanation", "Created Thread");
        nativeHandles.push_back(threads[N].native_handle());
        SMTRAT_LOG_TRACE("smtrat.mcsat.explanation", "Store Thread");

        explain<N+1>(data, var, reason, NUM_THREADS, mtx, threads, nativeHandles, counter, explanations);
    }

public:
    std::optional<Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
        const std::size_t NUM_THREADS = std::tuple_size<B>::value;
        if(NUM_THREADS <= 0){
            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "No explanation given.");
            return std::nullopt;
        }

        std::mutex mtx;
        std::vector<std::thread> threads;
        std::vector<pthread_t> nativeHandles;
        size_t counter = 0;
        std::vector<std::optional<Explanation>> explanations(NUM_THREADS, std::nullopt);

        mtx.lock();
        // same workarround as in sequential explanation
        std::optional<Explanation> explanation = explain<0>(data, var, reason, NUM_THREADS, mtx, threads, nativeHandles, counter, explanations);
        SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Explanation returned");
        return explanation;
	}

};

} // namespace mcsat
} // namespace smtrat
