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
 * @file ThreadPool.cpp
 *
 * @author  Henrik Schmitz
 * @since   2013-01-03
 * @version 2013-02-01
 */

#include "ThreadPool.h"
#include "Module.h"

using namespace std;

namespace smtrat
{
    ThreadPool::ThreadPool( unsigned _numberOfThreads, unsigned _numberOfCores ):
        mDone( false ),
        mPossibleOversubscription( _numberOfCores<_numberOfThreads ),
        mNumberOfCores( _numberOfCores ),
        mNumberOfThreads( _numberOfThreads ),
        mNumberOfRunningThreads( 1 ),
        mThreads( (_numberOfThreads-1), NULL ),
        mConditionVariables( _numberOfThreads ),
        mTasks( _numberOfThreads, packaged_task() )
    {
        mOversubscriptionFlags = vector<bool>( _numberOfThreads, true );
        if( mPossibleOversubscription )
            mThreadPriorityQueue = ThreadPriorityQueue();
    }

    ThreadPool::~ThreadPool()
    {
        mDone = true;
        while( !mTasks.empty() )
        {
            packaged_task toBeDeleted = mTasks.back();
            mTasks.pop_back();
            toBeDeleted.reset();
        }
        // No pointer deletion, threads need to terminate in native way
        while( !mThreads.empty() )
            mThreads.pop_back();
    }

    /**
     * 
     * @param _threadId
     */
    void ThreadPool::consumeBackend( unsigned _threadId )
    {
        thread_priority nextThreadPriority;
        std::unique_lock<std::mutex> lock( mMutex );
        while( !mDone )
        {
            mConditionVariables[ _threadId ].wait( lock, [ this, _threadId ](){ return mTasks[ _threadId ]!=packaged_task() && mOversubscriptionFlags[ _threadId ]; } );
            if( mPossibleOversubscription )
                mOversubscriptionFlags[ _threadId ] = false;
            packaged_task task = std::move( mTasks[ _threadId ] );
            lock.unlock();
            (*task)();
            lock.lock();
            if( mPossibleOversubscription )
            {
                if( mThreadPriorityQueue.pop( nextThreadPriority ) )
                {
                    mOversubscriptionFlags[ nextThreadPriority.first ] = true;
                    mConditionVariables[ nextThreadPriority.first ].notify_one();
                }
                else
                    --mNumberOfRunningThreads;
            }
        }
    }

    /**
     * 
     * @param _pModule
     */
    void ThreadPool::checkBackendPriority( Module* _pModule )
    {
        assert(mNumberOfRunningThreads <= mNumberOfCores);
        if( mPossibleOversubscription )
        {
            thread_priority threadPriority = _pModule->threadPriority();
            assert(threadPriority.first < mNumberOfThreads);
            thread_priority nextThreadPriority;
            std::unique_lock<std::mutex> lock( mMutex );
            if( !mThreadPriorityQueue.higherPriority( threadPriority.second ) )
            {
                if( mThreadPriorityQueue.pop( nextThreadPriority ) )
                {
                    mOversubscriptionFlags[ nextThreadPriority.first ] = true;
                    mConditionVariables[ nextThreadPriority.first ].notify_one();
                }
                else
                    --mNumberOfRunningThreads;
                mOversubscriptionFlags[ threadPriority.first ] = false;
                mThreadPriorityQueue.push( threadPriority );
                mConditionVariables[ threadPriority.first ].wait( lock, [ this, threadPriority ](){ return mOversubscriptionFlags[ threadPriority.first ]; } );
            }
        }
    }

    /**
     * 
     * @param _pModule
     * @return 
     */
    std::future<Answer> ThreadPool::submitBackend( Module* _pModule )
    {
        assert(mNumberOfRunningThreads <= mNumberOfCores);
        thread_priority threadPriority = _pModule->threadPriority();
        assert(threadPriority.first < (mNumberOfThreads-1));
        std::packaged_task<Answer()> task( std::bind( &Module::isConsistent, _pModule ) );
        std::future<Answer> result( task.get_future() );
        std::lock_guard<std::mutex> lock( mMutex );
        mTasks[ threadPriority.first ] = std::make_shared< std::packaged_task<Answer()> >( std::move( task ) );
        if( mThreads[ threadPriority.first ]==NULL )
        {
            try
            {
                if( mPossibleOversubscription )
                {
                    if( mNumberOfRunningThreads<mNumberOfCores )
                        ++mNumberOfRunningThreads;
                    else
                    {
                        mOversubscriptionFlags[ threadPriority.first ] = false;
                        mThreadPriorityQueue.push( threadPriority );
                    }
                }
                mThreads[ threadPriority.first ] = new std::thread( &ThreadPool::consumeBackend, this, threadPriority.first );
            }
            catch( std::exception &e )
            {
                mDone = true;
                printf("Caught %s\n", e.what());
                throw;
            }
        }
        else
        {
            if( mPossibleOversubscription )
            {
                if( mNumberOfRunningThreads<mNumberOfCores )
                {
                    ++mNumberOfRunningThreads;
                    mOversubscriptionFlags[ threadPriority.first ] = true;
                    mConditionVariables[ threadPriority.first ].notify_one();
                }
                else
                {
                    mOversubscriptionFlags[ threadPriority.first ] = false;
                    mThreadPriorityQueue.push( threadPriority );
                }
            }
            else
                mConditionVariables[ threadPriority.first ].notify_one();
        }
        return result;
    }
}    // namespace smtrat