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
			delete task;
			std::lock_guard<std::mutex> lock(mMutex);
			if (!mContinues.empty()) {
				mCounter--;
				mContinues.top().second = true;
				mContinues.top().first->notify_one();
				return;
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
		mCounter--;
		std::condition_variable cv;
		std::unique_lock<std::mutex> lock(mContinueMutex);
		mContinues.emplace(&cv, false);
		std::vector<std::future<Answer>> futures;
		for (const auto& m: _modules) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "\tCreating task for " << m->moduleName());
			Task* task = new Task(std::bind(&Module::check, m, _final, _full, _minimize), m);
			futures.emplace_back(task->getFuture());
			submitBackend(task);
		}
		cv.wait(lock, [&](){ return mContinues.top().second; });
		mContinues.pop();
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
