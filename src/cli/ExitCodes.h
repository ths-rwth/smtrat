/*
 * File:   ExitCodes.h
 * Author: Sebastian Junges
 *
 * Created on November 19, 2012, 10:42 AM
 */

#pragma once

constexpr int SMTRAT_EXIT_UNDEFINED			= -1;
constexpr int SMTRAT_EXIT_USERABORT			= 0;
constexpr int SMTRAT_EXIT_SUCCESS			= 1;
constexpr int SMTRAT_EXIT_SAT				= 2;
constexpr int SMTRAT_EXIT_UNSAT				= 3;
constexpr int SMTRAT_EXIT_UNKNOWN			= 4;
constexpr int SMTRAT_EXIT_WRONG_ANSWER		= 5;
constexpr int SMTRAT_EXIT_GENERALERROR		= 6;
constexpr int SMTRAT_EXIT_UNEXPECTED_ANSWER	= 7;
constexpr int SMTRAT_EXIT_UNEXPECTED_INPUT	= 8;
constexpr int SMTRAT_EXIT_NOSUCHFILE		= 9;
constexpr int SMTRAT_EXIT_PARSERFAILURE		= 10;
constexpr int SMTRAT_EXIT_TIMEOUT			= 11;
constexpr int SMTRAT_EXIT_MEMOUT			= 12;

