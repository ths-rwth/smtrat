namespace smtrat {
    class VarSchedulerBase;

    class VarSchedulerMinisat;
    
    template<mcsat::VariableOrdering vot>
    class VarSchedulerMcsatBooleanFirst;

    template<int lookahead, mcsat::VariableOrdering vot>
    class VarSchedulerMcsatUnivariateConstraintsOnly;
}