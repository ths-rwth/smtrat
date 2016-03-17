#pragma once

#include <chrono>
#include <condition_variable>
#include <future>
#include <stack>
#include <tuple>
#include <vector>

#include "../Common.h"

namespace smtrat {

class Module;

using Priority = std::vector<std::size_t>;

class Task {
private:
	std::packaged_task<Answer()> mTask;
	const Module* mModule;
public:
	template<typename T>
	Task(T&& task, const Module* module): mTask(std::move(task)), mModule(module) {}
	
	void run() {
		mTask();
	}
	const Module* getModule() const {
		return mModule;
	}
	std::future<Answer> getFuture() {
		return mTask.get_future();
	}
	
	bool operator<(const Task& rhs) const {
		return mModule->threadPriority() < rhs.mModule->threadPriority();
	}
};

class ThreadManager {
private:
	const std::size_t mMaxThreads;
	// Initialized with 1: There is always the main thread in the beginning.
	std::atomic<std::size_t> mCounter;
	std::mutex mContinueMutex;
	std::mutex mMutex;
	std::stack<std::pair<std::condition_variable*,bool>> mContinues;
	std::priority_queue<Task*> mQueue;
	
	void runTask(Task* task) {
		mCounter++;
		while (true) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "Executing " << task->getModule()->moduleName());
			task->run();
			SMTRAT_LOG_DEBUG("smtrat.parallel", "done.");
			delete task;
			std::lock_guard<std::mutex> lockA(mMutex);
			std::lock_guard<std::mutex> lockB(mContinueMutex);
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
	
	void submitBackend(Task* task) {
		SMTRAT_LOG_DEBUG("smtrat.parallel", "Submitting " << task->getModule()->moduleName());
		std::lock_guard<std::mutex> lock(mMutex);
		if (mCounter < mMaxThreads) {
			std::thread(&ThreadManager::runTask, this, task).detach();
		} else {
			mQueue.push(task);
		}
	}
public:	
	ThreadManager(std::size_t maxThreads): mMaxThreads(maxThreads), mCounter(1) {
	}
	~ThreadManager() {
	}
	
	Answer runBackends(const std::vector<Module*>& modules, bool final, bool full, bool minimize) {
        if( modules.empty() )
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
		for (const auto& m: modules) {
			SMTRAT_LOG_DEBUG("smtrat.parallel", "\tCreating task for " << m->moduleName());
			Task* task = new Task(std::bind(&Module::check, m, final, full, minimize), m);
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
};

}
