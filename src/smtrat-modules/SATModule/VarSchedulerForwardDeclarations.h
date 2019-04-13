namespace smtrat {
    class VarSchedulerBase;

    class VarSchedulerMinisat;
    class VarSchedulerRandom;
    class VarSchedulerFixedRandom;
    
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatBooleanFirst;
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatTheoryFirst;
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatActivityPreferTheory;
    template<int lookahead, mcsat::VariableOrdering vot>
    class VarSchedulerMcsatUnivariateConstraintsOnly;
}