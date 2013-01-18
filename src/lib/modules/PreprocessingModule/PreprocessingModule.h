/** 
 * @file   PreprocessingModule.h
 *         Created on January 10, 2013, 9:59 PM
 * @author: Sebastian Junges
 *
 * 
 */

#pragma once

#include "../Module.h"

namespace smtrat
{
    class PreprocessingModule : public Module
    {
        protected:

        public:
            /**
             * Constructors:
             */
            PreprocessingModule( const Formula* const, Manager* const _tsManager );

            /**
             * Destructor:
             */
            virtual ~PreprocessingModule();

            /**
             * Methods:
             */

            // Interfaces.
            bool assertSubformula( Formula::const_iterator );
            Answer isConsistent();
            void removeSubformula( Formula::const_iterator );
    };

}    // namespace smtrat

