#include "ContractionCandidate.h"
#include "IcpVariable.h"

namespace smtrat
{
    namespace icp{
        void ContractionCandidate::addOrigin( const FormulaT& _origin )
        {
            if( mOrigin.empty() )
            {
                for( IcpVariable* icpVar : mIcpVariables )
                    icpVar->incrementActivity();
            }
            assert(_origin.getType() == carl::FormulaType::CONSTRAINT);
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