#pragma once

namespace smtrat 
{
    /**
     * A class to save the current state of a GroebnerModule.
     * Used for backtracking-support
     */
    template<typename Settings>
    class GroebnerModuleState
    {
    public:
        GroebnerModuleState( ) :
        mRewrites()
        {

        }

        GroebnerModuleState( const GiNaCRA::Buchberger<typename Settings::Order>& basis, const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> >& rewrites ) :
        mBasis( basis ), mRewrites(rewrites)
        {
        }

        const GiNaCRA::Buchberger<typename Settings::Order>& getBasis( ) const
        {
            return mBasis;
        }

        const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> >& getRewriteRules() const
        {
            return mRewrites;
        }

    protected:
        ///The state of the basis
        const GiNaCRA::Buchberger<typename Settings::Order> mBasis;
        const std::map<unsigned, std::pair<Term, GiNaCRA::BitVector> > mRewrites;
    };
}