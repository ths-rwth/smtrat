namespace smtrat {
    class VarSchedulerBase;
    template<mcsat::VariableOrdering vot>
    class TheoryVarSchedulerStatic;

    class VarSchedulerMinisat;
    class VarSchedulerRandom;
    class VarSchedulerFixedRandom;

    enum class TheoryGuidedDecisionHeuristicLevel : unsigned { CONFLICT_FIRST, SATISFIED_FIRST, DISABLED };
    template<TheoryGuidedDecisionHeuristicLevel theory_conflict_guided_decision_heuristic>
    class VarSchedulerSMTTheoryGuided;
    
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatBooleanFirst;
    template<typename TheoryScheduler>
    class VarSchedulerMcsatTheoryFirst;
    template<typename TheoryScheduler,bool boolean_static>
    class VarSchedulerMcsatTheoryFirstBooleanMoreFirst;
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatActivityPreferTheory;
    template<int lookahead, mcsat::VariableOrdering vot>
    class VarSchedulerMcsatUnivariateConstraintsOnly;
    template<typename TheoryScheduler, bool respectActivities>
    class VarSchedulerMcsatUnivariateClausesOnly;
}