/* 
 * File:   VSSettings.h
 * Author: florian
 *
 * Created on 02 July 2013, 10:57
 */

#ifndef VSSETTINGS_H
#define	VSSETTINGS_H

#include "../../config.h"


namespace smtrat
{   
    struct VSSettings1
    {
        static const bool elimination_with_factorization                        = true;
        static const bool local_conflict_search                                 = true;
        static const bool use_strict_inequalities_for_test_candidate_generation = true;
        #ifdef SMTRAT_VS_VARIABLEBOUNDS
        static const bool use_variable_bounds                                   = true;
        #else
        static const bool use_variable_bounds                                   = false;
        #endif
        static const bool sturm_sequence_for_root_check                         = use_variable_bounds && true;
        static const bool check_conflict_for_side_conditions                    = true;
        static const bool incremental_solving                                   = true;
        static const bool infeasible_subset_generation                          = true;
        static const bool virtual_substitution_according_paper                  = true;
        static const bool prefer_equation_over_all                              = true;
    };
}

#endif	/* VSSETTINGS_H */

