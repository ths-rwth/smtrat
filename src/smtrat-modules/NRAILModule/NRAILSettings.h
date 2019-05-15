/**
 * @file AbstractSettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2018-07-12
 * Created on 2018-07-12.
 */

#pragma once

#include "factory/AxiomFactory.h"

namespace smtrat
{
    enum class UNSATFormulaSelectionStrategy {ALL = 0, FIRST = 1, RANDOM = 2};

	struct NRAILSettings1
	{
		static constexpr auto moduleName = "NRAILModule<NRAILSettings1>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
														  AxiomFactory::AxiomType::TANGENT_PLANE,
														  AxiomFactory::AxiomType::ICP,
														  AxiomFactory::AxiomType::CONGRUENCE,
														  AxiomFactory::AxiomType::MONOTONICITY};
	};

    struct NRAILSettings2
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings2>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings3
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings3>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings4
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings4>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings5
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings5>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings6
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings6>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings7
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

    struct NRAILSettings8
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings8>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings9
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings9>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings10
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings10>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings11
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings11>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings12
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings12>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings13
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings13>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::FIRST;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings14
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

    struct NRAILSettings15
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings15>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings16
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings16>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings17
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings17>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings18
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings18>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings19
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings19>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings20
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings20>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::CONGRUENCE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::MONOTONICITY};
    };

    struct NRAILSettings21
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings21>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::RANDOM;

        static constexpr AxiomFactory::AxiomType axiomType[5] = {AxiomFactory::AxiomType::MONOTONICITY,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

//    Experiment

    struct NRAILSettings22
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings22>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[4] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

    struct NRAILSettings23
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings23>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[4] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

    struct NRAILSettings24
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings24>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[6] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

    struct NRAILSettings25
    {
        static constexpr auto moduleName = "NRAILModule<NRAILSettings25>";

        static constexpr UNSATFormulaSelectionStrategy formulaSelectionStrategy = UNSATFormulaSelectionStrategy::ALL;

        static constexpr AxiomFactory::AxiomType axiomType[6] = {AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::TANGENT_PLANE,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::ZERO,
                                                                 AxiomFactory::AxiomType::ICP,
                                                                 AxiomFactory::AxiomType::CONGRUENCE};
    };

}
