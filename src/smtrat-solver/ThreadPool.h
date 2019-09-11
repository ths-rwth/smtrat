/**
 * @file ThreadPool.h
 *
 * @author  Gereon Kremer
 * @since   2016-03-18
 */

#pragma once

#include <smtrat-common/smtrat-common.h>

#include <chrono>
#include <condition_variable>
#include <future>
#include <stack>
#include <tuple>
#include <vector>

namespace smtrat {

class Module;

using Priority = std::vector<std::size_t>;

class Task {
private:
	std::packaged_task<Answer()> mTask;
	const Module* mModule;
    std::size_t mConditionalIndex;
public:
	template<typename T>
	Task(T&& task, const Module* module, std::size_t _index): mTask(std::move(task)), mModule(module), mConditionalIndex(_index) {}
	
	void run() {
		mTask();
	}
    
	const Module* getModule() const {
		return mModule;
	}
    
	std::size_t conditionalIndex() const {
		return mConditionalIndex;
	}
    
	std::future<Answer> getFuture() {
		return mTask.get_future();
	}
	
	bool operator<(const Task& rhs) const;
};

class BackendSynchronisation {
private:
	std::condition_variable mConditionVariable;
	std::mutex mMutex;
    bool mFireFlag;
public:
	BackendSynchronisation(): mConditionVariable(), mMutex(), mFireFlag(false) {}
	void wait() {
		std::unique_lock<std::mutex> lock(mMutex);
		mConditionVariable.wait(lock, [&](){ return mFireFlag; });
	}
	void notify() {
		std::lock_guard<std::mutex> lock(mMutex);
		mFireFlag = true;
		mConditionVariable.notify_one();
	}
};

class ThreadPool {
private:
    ///
	const std::size_t mMaxThreads;
	/// Initialized with 1: There is always the main thread in the beginning.
	std::atomic<std::size_t> mCounter;
	/// Initialized with 1: There is always the main thread in the beginning.
	std::atomic<std::size_t> mNumberThreads;
    ///
	std::mutex mBackendSynchrosMutex;
    ///
	std::vector<BackendSynchronisation*> mBackendSynchros;
    ///
	std::mutex mQueueMutex;
    ///
	std::mutex mThreadCreationMutex;
	///
	std::priority_queue<Task*> mQueue;
	
	bool shallBeSkipped(std::size_t index) {
		std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
		return index >= mBackendSynchros.size() || mBackendSynchros[index] == nullptr;
	}
	bool notify(std::size_t index) {
		std::lock_guard<std::mutex> bsLock(mBackendSynchrosMutex);
		if (index < mBackendSynchros.size() && mBackendSynchros[index] != nullptr) {
			mBackendSynchros[index]->notify();
			return true;
		}
		return false;
	}
	
    /**
     * 
     * @param task
     */
	void runTask(Task* task);
    void deleteTask(Task* task) {
        delete task;
        --mNumberThreads;
    }
	
    /**
     * 
     * @param task
     */
	void submitBackend(Task* task);
public:	
	ThreadPool(std::size_t maxThreads): mMaxThreads(maxThreads), mCounter(1), mNumberThreads(1) {}
    
	~ThreadPool()
    {
        while(mNumberThreads>1);
    }
	
    /**
     * @param _modules
     * @param _final
     * @param _full
     * @param _objective
     */
	Answer runBackends(const std::vector<Module*>& _modules, bool _final, bool _full, carl::Variable::Arg _objective);
};

}
