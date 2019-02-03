/**
 * @file AbstractSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#pragma once

#include "../ModuleSettings.h"
#include "factory/AxiomFactory.h"

namespace smtrat
{
	struct NRAILSettings1 : ModuleSettings
	{
		static constexpr auto moduleName = "NRAILModule<NRAILSettings1>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
														  AxiomFactory::AxiomType::TANGENT_PLANE,
														  AxiomFactory::AxiomType::ICP,
														  AxiomFactory::AxiomType::CONGRUENCE,
														  AxiomFactory::AxiomType::MONOTONICITY};
	};

    struct NRAILSettings2 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings2>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings3 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings3>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings4 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings4>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings5 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings5>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings6 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings6>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings7 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings7>";

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::MONOTONICITY,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };
}
