/*
 * SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */
/**
 * @file IntBlastSettings.h
 * @author Andreas Krueger <andreas.krueger@rwth-aachen.de>
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 */


#pragma once

#include "../../solver/ModuleSettings.h"

namespace smtrat
{
    struct IntBlastSettings1 : ModuleSettings
    {
		static constexpr auto moduleName = "IntBlastModule<IntBlastSettings1>";
        /**
         * Maximum width used for encoding an integer variable as bit-vector.
         *
         * Note that this only applies to the encoding of variables.
         * Intermediate terms (polynomials) are always encoded using a
         * sufficiently high width.
         * 
         * If this value is set to zero, there is no maximal width. Choose this option only if all variables are bounded.
         */
        static const std::size_t max_variable_encoding_width = 6;

        /**
         * Whether to allow the encoding into complex bit-vector terms.
         * When set to false, an own bit-vector variable is introduced for
         * each encoded polynomial.
         * When set to true, polynomials may also be encoded by bit-vector terms
         * that consist of bit-vector function symbols.
         */
        static const bool allow_encoding_into_complex_bvterms = true;

        /**
         * Whether to apply ICP to obtain smaller bounds for the
         * term encodings.
         * If set to false, the widths for the encoded bit-vector terms
         * are chosen conservatively.
         */
        static const bool apply_icp = false;

        /**
         * Whether to use offsets for annotated bit-vector terms.
         * For nonlinear variables, no offset is used (independent of this
         * configuration setting).
         */
        static const bool use_offsets_in_encoding = false;
    };
    
    struct IntBlastSettings2 : IntBlastSettings1
    {
		static constexpr auto moduleName = "IntBlastModule<IntBlastSettings2>";
        static const std::size_t max_variable_encoding_width = 0;
    };
}
