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
    enum class UNSATFormulaSelectionStrategy {ALL = 0, FIRST = 1, RANDOM = 2};

	struct NRAILSettings1 : ModuleSettings
	{
		static constexpr auto moduleName = "NRAILModule<NRAILSettings1>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
														  AxiomFactory::AxiomType::TANGENT_PLANE,
														  AxiomFactory::AxiomType::ICP,
														  AxiomFactory::AxiomType::CONGRUENCE,
														  AxiomFactory::AxiomType::MONOTONICITY};
	};

    struct NRAILSettings2 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings2>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings3 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings3>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings4 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings4>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings5 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings5>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings6 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings6>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings7 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings7>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::MONOTONICITY,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

//    First

    struct NRAILSettings8 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings8>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings9 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings9>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings10 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings10>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings11 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings11>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings12 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings12>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings13 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings13>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings14 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings14>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::MONOTONICITY,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

//    Random

    struct NRAILSettings15 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings15>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings16 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings16>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings17 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings17>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings18 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings18>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings19 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings19>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings20 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings20>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings21 : ModuleSettings
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings21>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::MONOTONICITY,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

}
