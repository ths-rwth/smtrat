/**
 * @file ThreadPool.cpp
 *
 * @author  Gereon Kremer
 * @since   2016-03-18
 */

#include "ThreadPool.h"
#include <smtrat-solver/Module.h>

namespace smtrat
{
    bool Task::operator<(const Task& rhs) const {
		return mModule->threadPriority() < rhs.mModule->threadPriority();
	}
    
    void ThreadPool::runTask(Task* task) {
		mCounter++;
		while (true) {
			std::size_t index = task->conditionalIndex();
			bool skipTask = shallBeSkipped(index);
			if (!skipTask) {
				SMTRAT_LOG_DEBUG("smtrat.parallel", "Executing " << task->getModule()->moduleName());
                task->run();
				SMTRAT_LOG_DEBUG("smtrat.parallel", "done.");
                deleteTask(task);
				if (notify(index)) {
					mCounter--;
					return;
				}
			} else {
				deleteTask(task);
			}
			std::lock_guard<std::mutex> lock(mQueueMutex);
			if (mQueue.empty()) {
				mCounter--;
				return;
			}
			task = mQueue.top();
			mQueue.pop();
		}
	}
    
    void ThreadPool::submitBackend(Task* task) {
		SMTRAT_LOG_DEBUG("smtrat.parallel", "Submitting " << task->getModule()->moduleName());
        /*auto tmpCounter =*/ mCounter.load();
		//if (tmpCounter < mMaxThreads) { // TODO: Counter does currently not work correctly
            std::thread(&ThreadPool::runTask, this, task).detach();
		/*} else {
			std::lock_guard<std::mutex> lock(mQueueMutex);
			mQueue.push(task);
		}*/
	}
    
	Answer ThreadPool::runBackends(const std::vector<Module*>& _modules, bool _final, bool _full, carl::Variable _objective) {
        if( _modules.empty() )
        {
            SMTRAT_LOG_DEBUG("smtrat.parallel", "Returning " << UNKNOWN);
            return UNKNOWN;
        }
		assert(mCounter > 0);
        std::size_t index = 0;
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
            index = mBackendSynchros.size();
            mBackendSynchros.push_back(new BackendSynchronisation());
        }
		std::vector<std::future<Answer>> futures;
		for (const auto& m: _modules) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "\tCreating task for " << m->moduleName());
            Task* task = new Task(std::bind(&Module::check, m, _final, _full, _objective), m, index);
            ++mNumberThreads;
			futures.emplace_back(task->getFuture());
			submitBackend(task);
		}
        // wait until one task (backend check) fires the condition variable which means it has finished its check
        BackendSynchronisation* bs;
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
            bs = mBackendSynchros[index];
        }
		mCounter--;
        bs->wait();
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
			delete mBackendSynchros[index];
			mBackendSynchros[index] = nullptr;
			while (!mBackendSynchros.empty() && mBackendSynchros.back() == nullptr) {
				mBackendSynchros.pop_back();
			}
        }
		mCounter++;
		Answer res = Answer::ABORTED;
		for (auto& f: futures) {
            Answer ans = Answer::ABORTED;
            try
            {
                ans = f.get();
            }
            catch(const std::exception& e)
            {
                // If backend A returned before backend B 
                // TODO: This might also happen, if A return Unknown .. see for notify(..)
            }
            switch (ans) {
				case Answer::ABORTED: break;
				case Answer::UNKNOWN:
                {
                    if( res == Answer::ABORTED )
                        res = Answer::UNKNOWN;
                    break;
                }
				case Answer::OPTIMAL:
				case Answer::SAT:
                {
                    assert( res != Answer::UNSAT );
                    res = ans;
                    break;
                }
				case Answer::UNSAT:
                {
                    assert( res != Answer::SAT );
                    res = Answer::UNSAT;
                    break;
                }
            }
		}
		SMTRAT_LOG_DEBUG("smtrat.parallel", "Returning " << res);
        return res;
	}
}    // namespace smtrat
