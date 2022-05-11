#include "ContractionCandidate.h"
#include "IcpVariable.h"

namespace smtrat
{
    namespace icp{

#ifdef __VS
        const double ContractionCandidate::mAlpha = 0.9;
#endif

        void ContractionCandidate::addOrigin( const FormulaT& _origin )
        {
            if( mOrigin.empty() )
            {
                for( IcpVariable* icpVar : mIcpVariables )
                    icpVar->incrementActivity();
            }
            assert(_origin.type() == carl::FormulaType::CONSTRAINT);
            mOrigin.insert(_origin);
        }

        void ContractionCandidate::removeOrigin( const FormulaT& _origin )
        {
            mOrigin.erase(_origin);
            if( mOrigin.empty() )
            {
                for( IcpVariable* icpVar : mIcpVariables )
                    icpVar->decrementActivity();
            }
        }
    }
}