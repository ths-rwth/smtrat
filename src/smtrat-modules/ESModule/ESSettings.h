/**
 * @file ESSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2015-09-09
 * Created on 2015-09-09.
 */

#pragma once

namespace smtrat
{
    struct ESSettingsDefault
    {
		static constexpr auto moduleName = "ESModule<ESSettingsDefault>";
        
        static const std::size_t substitution_bitsize_limit = 0; // no limit
    };

    struct ESSettingsLimitSubstitution
    {
		static constexpr auto moduleName = "ESModule<ESSettingsLimitSubstitution>";
        
        // limit the bitsize of substitution to avoid explosion of coefficients
        static const std::size_t substitution_bitsize_limit = 500;
    };
}
