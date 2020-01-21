# IntEqModule {#IntEqModule}

Implements the SMT compliant equation elimination method presented in @cite Griggio2012.
Hence, this module either determines that the equations of an instance are unsatisfiable
or calculates a certain number of substitutions for variables. The latter can be used to 
eliminate the equations by substituting every variable for which a substitution exists
by its substitution. The set of constraints that we obtain with this procedure, not containing equations 
anymore, is passed to the backends.