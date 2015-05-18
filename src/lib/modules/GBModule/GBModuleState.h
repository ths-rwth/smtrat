#pragma once

namespace smtrat 
{
    /**
     * A class to save the current state of a GBModule.
     * Used for backtracking-support
     */
    template<typename Settings>
    class GBModuleState
    {
    public:
        GBModuleState( ) :
        mRewrites()
        {

        }

        GBModuleState( const typename Settings::Groebner& basisCalculation, const std::map<carl::Variable, std::pair<TermT, carl::BitVector> >& rewrites ) :
        mBasis( basisCalculation ), mRewrites(rewrites)
        {
        }

        const typename Settings::Groebner& getBasis( ) const
        {
            return mBasis;
        }

        const std::map<carl::Variable, std::pair<TermT, carl::BitVector> >& getRewriteRules() const
        {
            return mRewrites;
        }

    protected:
        ///The state of the basis
        const typename Settings::Groebner mBasis;
        const std::map<carl::Variable, std::pair<TermT, carl::BitVector> > mRewrites;
    };
}