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
    ThreadPool::ThreadPool( size_t _numberOfThreads, std::size_t _numberOfCores ):
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

    void ThreadPool::consumeBackend( std::size_t _threadId )
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

    std::future<Answer> ThreadPool::submitBackend( Module* _pModule, bool _full )
    {
        assert(mNumberOfRunningThreads <= mNumberOfCores);
        thread_priority threadPriority = _pModule->threadPriority();
        assert(threadPriority.first < (mNumberOfThreads-1));
        std::packaged_task<Answer()> task( std::bind( &Module::check, _pModule, _full ) );
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
