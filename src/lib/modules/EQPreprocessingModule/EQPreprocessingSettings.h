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
 * @file EQPreprocessingSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2014-12-05
 * Created on 2014-12-05.
 */

#pragma once

namespace smtrat {
	struct EQPreprocessingSettings1 {
#ifdef __VS
		static const std::string getModuleName() { return "EQPreprocessingModule<EQPreprocessingSettings1>"; }
#else
		static constexpr auto moduleName = "EQPreprocessingModule<EQPreprocessingSettings1>";
#endif
		static CONSTEXPR bool printFormulas = false;

		static CONSTEXPR bool rewriteFunctionInstances = false;

		static CONSTEXPR bool rewriteBooleanDomainConstraints = true;

		static CONSTEXPR bool performNNF = true;

		static CONSTEXPR bool rewriteUsingFacts = false;
	};

	struct EQPreprocessingSettings2 {
#ifdef __VS
		static const std::string getModuleName() { return "EQPreprocessingModule<EQPreprocessingSettings2>"; }
#else
		static constexpr auto moduleName = "EQPreprocessingModule<EQPreprocessingSettings2>";
#endif
		static CONSTEXPR bool printFormulas = false;

		static CONSTEXPR bool rewriteFunctionInstances = true;

		static CONSTEXPR bool rewriteBooleanDomainConstraints = true;

		static CONSTEXPR bool performNNF = true;

		static CONSTEXPR bool rewriteUsingFacts = false;
	};
}
