namespace smtrat {
    class VarSchedulerBase;

    class VarSchedulerMinisat;
    class VarSchedulerRandom;
    class VarSchedulerFixedRandom;
    
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatBooleanFirst;

    template<int lookahead, mcsat::VariableOrdering vot>
    class VarSchedulerMcsatUnivariateConstraintsOnly;
}