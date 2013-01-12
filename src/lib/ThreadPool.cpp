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
 * @version 2013-01-11
 */

#include "Module.h"
#include "ThreadPool.h"

using namespace std;

namespace smtrat
{
    
    ThreadPool::ThreadPool( unsigned _numberOfCores ):
        mDone( false ),
        mJoiner( mWorkerThreads )
    {
        try
        {
            for( unsigned i=0; i<_numberOfCores; ++i )
            {
                mWorkerThreads.push_back( std::thread( &ThreadPool::workerThread, this ) );
            }
        }
        catch( ... )
        {
            mDone = true;
            throw;
        }
    }

    ThreadPool::~ThreadPool()
    {
        mDone = true;
//        mThreadConditionVariable.notify_all();
    }

    void ThreadPool::workerThread()
    {
        prioritisedTask task;
        while( !mDone )
        {
            if( mTasks.pop( task ) )
            {
                (task.second)();
            }
            else
            {
//                std::unique_lock<std::mutex> lock( mMutex );
//                mThreadConditionVariable.wait( lock );
                std::this_thread::yield();
            }
        };
    }

    std::future<Answer> ThreadPool::submitTask( Module& _rModule )
    {
        std::packaged_task<Answer()> task( std::bind( &Module::isConsistent, &_rModule ) );
        std::future<Answer> result( task.get_future() );
        mTasks.push( std::move( prioritisedTask( _rModule.id(), std::move( task ) ) ) );
//        mThreadConditionVariable.notify_one();
        return result;
    }
}    // namespace smtrat