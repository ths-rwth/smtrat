# FPPModule {#FPPModule}

This module implements a generic preprocessing facility.
It runs a given strategy on the input and retrieves the simplified formula using the facilities of the [Manager](@ref smtrat::Manager) class.
This process is iterated until a fix point is reached -- no further simplification was done by the strategy -- or a predefined number of iterations was performed.
The resulting simplified formula is then forwarded to the backend.

The strategy should be a linear sequence of preprocessing modules, as passing simplified formulas back to the caller is not possible in a meaningful way for general [Module](@ref smtrat::Module) classes.
