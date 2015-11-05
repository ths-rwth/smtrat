/**
 * @file PolyTreePool.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 */

#pragma once

#include "carl/formula/bitvector/Pool.h"
#include "PolyTree.h"

namespace smtrat
{
    class PolyTreePool : public carl::Singleton<PolyTreePool>
    {
    private:
        friend carl::Singleton<PolyTreePool>;

        // The PolyTree pool. Each Poly is mapped to a corresponding PolyTreeContent.
        std::map<Poly, PolyTreeContent*> mPool;
        // Mutex to avoid multiple access to the pool
        mutable std::mutex mMutexPool;

        #define POOL_LOCK_GUARD std::lock_guard<std::mutex> lock( mMutexPool );
        #define POOL_LOCK mMutexPool.lock();
        #define POOL_UNLOCK mMutexPool.unlock();

    protected:

        /**
         * Constructor of the pool.
         */
        PolyTreePool() :
        mPool()
        { }

        ~PolyTreePool()
        {
            std::map<Poly, PolyTreeContent*>::iterator it = mPool.begin();
            while(it != mPool.end()) {
                delete it->second;
                it = mPool.erase(it);
            }
        }

    public:

        const PolyTreeContent* get(const Poly& _pol);

    private:

        const PolyTreeContent* create(const Poly& _pol);
        const PolyTreeContent* create(carl::Variable::Arg _variable);
        const PolyTreeContent* create(Integer _constant);
        const PolyTreeContent* create(const Poly& _poly, PolyTree::Type _type, const Poly& _left, const Poly& _right);

        const PolyTreeContent* add(PolyTreeContent* _element);
    };
}
