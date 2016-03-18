/**
 * @file ThreadPool.h
 *
 * @author  Gereon Kremer
 * @since   2016-03-18
 */

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
	
	bool operator<(const Task& rhs) const;
};

class ThreadPool {
private:
    ///
	const std::size_t mMaxThreads;
	/// Initialized with 1: There is always the main thread in the beginning.
	std::atomic<std::size_t> mCounter;
    ///
	std::mutex mContinueMutex;
    ///
	std::mutex mMutex;
    ///
	std::stack<std::pair<std::condition_variable*,bool>> mContinues;
    ///
	std::priority_queue<Task*> mQueue;
	
    /**
     * 
     * @param task
     */
	void runTask(Task* task);
	
    /**
     * 
     * @param task
     */
	void submitBackend(Task* task);
public:	
	ThreadPool(std::size_t maxThreads): mMaxThreads(maxThreads), mCounter(1) {}
    
	~ThreadPool() {}
	
    /**
     * @param _modules
     * @param _final
     * @param _full
     * @param _minimize
     */
	Answer runBackends(const std::vector<Module*>& _modules, bool _final, bool _full, bool _minimize);
};

}
