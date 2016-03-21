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
		if (mCounter < mMaxThreads) {
			std::thread(&ThreadPool::runTask, this, task).detach();
		} else {
			std::lock_guard<std::mutex> lock(mQueueMutex);
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
        std::size_t index = 0;
		{
            std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
            index = mBackendSynchros.size();
            mBackendSynchros.push_back(new BackendSynchronisation());
        }
		std::vector<std::future<Answer>> futures;
		for (const auto& m: _modules) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "\tCreating task for " << m->moduleName());
			Task* task = new Task(std::bind(&Module::check, m, _final, _full, _minimize), m, index);
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
            Answer ans = f.get();
            switch (ans) {
				case Answer::ABORTED: break;
				case Answer::UNKNOWN: res = Answer::UNKNOWN; break;
				case Answer::SAT: return Answer::SAT;
				case Answer::UNSAT: return Answer::UNSAT;
            }
		}
		SMTRAT_LOG_DEBUG("smtrat.parallel", "Returning " << res);
		return res;
	}
}    // namespace smtrat
