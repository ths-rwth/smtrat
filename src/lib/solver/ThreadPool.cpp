/**
 * @file ThreadPool.cpp
 *
 * @author  Gereon Kremer
 * @since   2016-03-18
 */

#include "ThreadPool.h"
#include "Module.h"

namespace smtrat
{
    bool Task::operator<(const Task& rhs) const {
		return mModule->threadPriority() < rhs.mModule->threadPriority();
	}
    
    void ThreadPool::runTask(Task* task) {
		mCounter++;
		while (true) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "Executing " << task->getModule()->moduleName());
			task->run();
			SMTRAT_LOG_DEBUG("smtrat.parallel", "done.");
            std::size_t index = task->conditionalIndex();
			delete task;
			std::lock_guard<std::mutex> lock(mMutex);
            {
                std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
                if(index < mBackendSynchros.size() && mBackendSynchros[index] != nullptr) {
                    mCounter--;
                    std::lock_guard<std::mutex> cvLock( mBackendSynchros[index]->rCVMutex() );
                    mBackendSynchros[index]->rFireFlag() = true;
                    mBackendSynchros[index]->rConditionVariable().notify_one();
                    return;
                }
            }
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
		std::lock_guard<std::mutex> lock(mMutex);
		if (mCounter < mMaxThreads) {
			std::thread(&ThreadPool::runTask, this, task).detach();
		} else {
			mQueue.push(task);
		}
	}
    
	Answer ThreadPool::runBackends(const std::vector<Module*>& _modules, bool _final, bool _full, bool _minimize) {
        if( _modules.empty() )
        {
            SMTRAT_LOG_DEBUG("smtrat.parallel", "Returning " << UNKNOWN);
            return UNKNOWN;
        }
		assert(mCounter > 0);
        std::size_t index;
		mCounter--;
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
            index = mBackendSynchros.size();
            mBackendSynchros.push_back(new BackendSynchronisation());
        }
		std::vector<std::future<Answer>> futures;
		for (const auto& m: _modules) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "\tCreating task for " << m->moduleName());
			Task* task = new Task(std::bind(&Module::check, m, _final, _full, _minimize), m, index);
			futures.emplace_back(task->getFuture());
			submitBackend(task);
		}
        // wait until one task (backend check) fires the condition variable which means it has finished its check
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
            std::unique_lock<std::mutex> lock(mBackendSynchros[index]->rCVMutex());
            mBackendSynchros[index]->rConditionVariable().wait(lock, [&](){ return mBackendSynchros[index]->fireFlag(); });
            delete mBackendSynchros[index];
            if( index == mBackendSynchros.size()-1 )
                mBackendSynchros.pop_back();
            else
                mBackendSynchros[index] = nullptr;
        }
		mCounter++;
		Answer res = Answer::ABORTED;
		for (auto& f: futures) {
			if (f.wait_for(std::chrono::seconds(0)) == std::future_status::ready) {
                Answer ans = f.get();
				switch (ans) {
				case Answer::ABORTED: break;
				case Answer::UNKNOWN: res = Answer::UNKNOWN; break;
				case Answer::SAT: return Answer::SAT;
				case Answer::UNSAT: return Answer::UNSAT;
				}
			}
		}
		SMTRAT_LOG_DEBUG("smtrat.parallel", "Returning " << res);
		return res;
	}
}    // namespace smtrat
