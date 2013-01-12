/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2013 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT. If not, see <http://www.gnu.org/licenses/>.
 *
 */

/**
 * @file ThreadPool.h
 *
 * @author  Henrik Schmitz
 * @since   2013-01-03
 * @version 2013-01-11
 */

#ifndef THREADPOOL_H
#define	THREADPOOL_H

#include <atomic>
#include <future>
#include <mutex>
#include <queue>
#include <thread>
#include <vector>

#include "Answer.h"

namespace smtrat
{
    class Module;
    
    typedef std::pair< unsigned, std::packaged_task<Answer()> > prioritisedTask;
    
    class ThreadPool
    {
        private:
            class JoinThreads
            {
                private:
                    std::vector<std::thread>& mrThreads;
                    
                public:
                    explicit JoinThreads( std::vector<std::thread>& _rThreads ):
                        mrThreads( _rThreads )
                    {}
                        
                    ~JoinThreads()
                    {
                        for( unsigned i=0; i<mrThreads.size(); ++i )
                        {
                            if( mrThreads[i].joinable() )
                            {
                                mrThreads[i].join();
                            }
                        }
                    }
            };
            
            class TaskQueue
            {
                private:
                    class CompareTasks
                    {
                        public:
                            bool operator()( const std::shared_ptr<prioritisedTask>& _rTask1, const std::shared_ptr<prioritisedTask>& _rTask2 )
                            {
                                if( _rTask1->first > _rTask2->first )
                                {
                                    return true;
                                }
                                else
                                {
                                    return false;
                                }
                            }
                    };
                    
                    mutable std::mutex mMutex;
                    std::priority_queue< std::shared_ptr<prioritisedTask>, std::vector< std::shared_ptr<prioritisedTask> >, CompareTasks > mQueue;

                public:
                    TaskQueue(){}
                    
                    ~TaskQueue(){}
                    
                    bool empty() const
                    {
                        std::lock_guard<std::mutex> lock( mMutex );
                        return mQueue.empty();
                    }
                    
                    bool pop( prioritisedTask& _rTask )
                    {
                        std::lock_guard<std::mutex> lock( mMutex );
                        if( mQueue.empty() )
                        {
                            return false;
                        }
                        _rTask = std::move( *mQueue.top() );
                        mQueue.pop();
                        return true;
                    }
                    
                    void push( prioritisedTask _newTask )
                    {
                        std::shared_ptr< prioritisedTask > task( std::make_shared< prioritisedTask >( std::move( _newTask ) ) );
                        std::lock_guard<std::mutex> lock( mMutex );
                        mQueue.push( task );
                    }
            };
            
            void workerThread();
            
            std::atomic_bool mDone;
            TaskQueue mTasks;
            std::vector<std::thread> mWorkerThreads;
            JoinThreads mJoiner;
//            std::mutex mMutex;
//            std::condition_variable mThreadConditionVariable;

        public:
            ThreadPool( unsigned );

            ~ThreadPool();

            std::future<Answer> submitTask( Module& );
    };
}    // namespace smtrat

#endif	/* THREADPOOL_H */