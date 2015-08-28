/**
 * @file ThreadPool.h
 *
 * @author  Henrik Schmitz
 * @since   2013-01-03
 * @version 2013-02-01
 */

#pragma once

#include <atomic>
#include <future>
#include <map>
#include <mutex>
#include <queue>
#include <thread>
#include <vector>

#include "../Common.h"

namespace smtrat
{

    // pair: first = thread id, second = priority
    typedef std::shared_ptr< std::packaged_task<Answer()> > packaged_task;
    
    class Module;

    class ThreadPool
    {
        private:

            class ThreadPriorityQueue
            {
                private:
                    class CompareThreadPriorities
                    {
                        public:
                            bool operator()( const std::shared_ptr<thread_priority>& _rThreadPriority1, std::shared_ptr<thread_priority>& _rThreadPriority2 )
                            {
                                if( (_rThreadPriority1->second)>(_rThreadPriority2->second) )
                                    return true;
                                else
                                    return false;
                            }
                    };

                    std::priority_queue< std::shared_ptr<thread_priority>, std::vector< std::shared_ptr<thread_priority> >, CompareThreadPriorities > mQueue;

                public:
                    ThreadPriorityQueue(){}
                    ~ThreadPriorityQueue(){}

                    bool empty() const
                    {
                        return mQueue.empty();
                    }

                    bool higherPriority( unsigned _priority ) const
                    {
                        return empty() || mQueue.top()->second>_priority;
                    }

                    bool pop( thread_priority& _rThreadPriority )
                    {
                        if( mQueue.empty() )
                            return false;
                        else
                        {
                            _rThreadPriority = std::move( *mQueue.top() );
                            mQueue.pop();
                            return true;
                        }
                    }

                    void push( thread_priority _newThreadPriority )
                    {
                        std::shared_ptr<thread_priority> value( std::make_shared<thread_priority>( std::move( _newThreadPriority ) ) );
                        mQueue.push( value );
                    }
            };
            
            // Members.
            std::mutex mMutex;
            std::atomic_bool mDone;
            std::atomic_bool mPossibleOversubscription;
            unsigned mNumberOfCores;
            size_t mNumberOfThreads;
            unsigned mNumberOfRunningThreads;
            std::vector<std::thread*> mThreads;
            std::vector<std::condition_variable> mConditionVariables;
            // Used as protection against spurious wake ups of condition variables
            std::vector<bool> mOversubscriptionFlags;
            std::vector<packaged_task> mTasks;
            ThreadPriorityQueue mThreadPriorityQueue;

            // Private methods.
            void consumeBackend( unsigned );

        public:
            // Constructor and destructor.
            ThreadPool( size_t, unsigned );
            ~ThreadPool();

            // Public methods.
            void checkBackendPriority( Module* );
            std::future<Answer> submitBackend( Module*, bool );
    };
}    // namespace smtrat
