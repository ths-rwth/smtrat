#pragma once

#include <boost/interprocess/managed_shared_memory.hpp>
#include <boost/interprocess/containers/vector.hpp>
#include <boost/interprocess/allocators/allocator.hpp>
#include <unistd.h>

#include "../utils/Bookkeeping.h"

#include <smtrat-common/smtrat-common.h>

namespace smtrat {
namespace mcsat {

using namespace boost::interprocess;
typedef allocator<boost::optional<Explanation> , managed_shared_memory::segment_manager>  ShmemAllocator;
typedef vector<boost::optional<Explanation> , ShmemAllocator> SharedVector;

/**
 * This explanation executes all given explanation in parallel processes and waits for the fastest explanation,
 * returning the fastest delivered explanation, terminating all other parallel processes
 */
//TODO make shared memory runnable
template<typename... Backends>
struct FastParallelExplanation {
private:
	using B = std::tuple<Backends...>;
	B mBackends;

    template<std::size_t N = 0, carl::EnableIfBool<N == std::tuple_size<B>::value> = carl::dummy>
    void explain(const mcsat::Bookkeeping&, carl::Variable, const FormulasT&, std::vector<pid_t>& pids) const {
        SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "All explanations started.");
    }

    template<std::size_t N = 0, carl::EnableIfBool<N < std::tuple_size<B>::value> = carl::dummy>
    void explain(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason, std::vector<pid_t>& pids) const {

        if( (pids[N] = fork()) == 0){
            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Concurrent strategy " << N+1 << " started");
            boost::optional<Explanation> explanation = std::get<N>(mBackends)(data, var, reason);
            SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Concurrent strategy " << N+1 << " done");

            managed_shared_memory segment(open_only, "SharedVector");
            SharedVector *explanations = segment.find<SharedVector>("ExplanationsVector").first;
            *(explanations->begin()+N) = explanation;

            //wait
            while (true){
                (void)0;
            }
            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "This should not be reachable");
        } else if(pids[N] == -1){
            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "Error while forking.");
        }

        explain<N+1>(data, var, reason, pids);
    }

public:
    boost::optional<Explanation> operator()(const mcsat::Bookkeeping& data, carl::Variable var, const FormulasT& reason) const {
        const std::size_t NUM_PROCESSES = std::tuple_size<B>::value;
        if(NUM_PROCESSES <= 0){
            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "No explanation given.");
            return boost::none;
        }

        struct shm_remove {
            shm_remove() { shared_memory_object::remove("MySharedMemory"); }
            ~shm_remove(){ shared_memory_object::remove("MySharedMemory"); }
        } remover;

        std::vector<pid_t> pids;

        managed_shared_memory segment(create_only, "SharedVector", 65536);
        const ShmemAllocator alloc_inst (segment.get_segment_manager());
        SharedVector *explanations = segment.construct<SharedVector>("ExplanationsVector")(alloc_inst);

        for(size_t i = 0; i < NUM_PROCESSES; i++) {
            explanations->push_back(boost::none);
        }

        // same workarround as in sequential explanation
        explain<0>(data, var, reason, pids);
        SMTRAT_LOG_DEBUG("smtrat.mcsat.explanation", "Start looking for explanation");
        while (true){
            for (auto it = explanations->begin(); it != explanations->end(); it++) {
                if((*it) != boost::none){
                    for (size_t i = 0; i < NUM_PROCESSES; i++) {
                        if(!kill(pids[i], SIGKILL)){
                            SMTRAT_LOG_ERROR("smtrat.mcsat.explanation", "Error in Kill.");
                        }
                    }

                    segment.destroy<SharedVector>("ExplanationsVector");
                    return *it;
                }
            }
        }

	}

};

} // namespace mcsat
} // namespace smtrat
