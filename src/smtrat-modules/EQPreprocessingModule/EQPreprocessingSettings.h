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
		static constexpr auto moduleName = "EQPreprocessingModule<EQPreprocessingSettings1>";
		static constexpr bool printFormulas = false;

		static constexpr bool rewriteFunctionInstances = false;

		static constexpr bool rewriteBooleanDomainConstraints = true;

		static constexpr bool performNNF = true;

		static constexpr bool rewriteUsingFacts = false;
	};

	struct EQPreprocessingSettings2 {
		static constexpr auto moduleName = "EQPreprocessingModule<EQPreprocessingSettings2>";
		static constexpr bool printFormulas = false;

		static constexpr bool rewriteFunctionInstances = true;

		static constexpr bool rewriteBooleanDomainConstraints = true;

		static constexpr bool performNNF = true;

		static constexpr bool rewriteUsingFacts = false;
	};
}
