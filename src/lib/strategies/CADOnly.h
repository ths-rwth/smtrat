/**
 * @file CADOnly.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/CADModule/CADModule.h"
#include "../modules/SATModule/SATModule.h"

namespace smtrat
{
	/**
	 * Strategy description.
	 *
	 * @author
	 * @since
	 * @version
	 *
	 */
	template<typename CADSetting>
	class CADOnlyStrategy: public Manager
	{
		public:
			CADOnlyStrategy(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<CADModule<CADSetting>>()
					})
				});
			}
	};
	
	using CADOnly = CADOnlyStrategy<CADSettingsReal>;
	using CADOnlyEarly = CADOnlyStrategy<CADSettingsSplitEarly>;
	using CADOnlyLazy = CADOnlyStrategy<CADSettingsSplitLazy>;
	using CADOnlySolution = CADOnlyStrategy<CADSettingsSplitSolution>;
	using CADOnlyGuess = CADOnlyStrategy<CADSettingsGuessAndSplit>;

}	// namespace smtrat
