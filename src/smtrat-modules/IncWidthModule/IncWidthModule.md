# IncWidthModule {#IncWidthModule}

This module is meant to be used for solving nonlinear integer arithmetic problems by encoding them into bitvector arithmetic formulas (as done in smtrat::IntBlastModule), as described in @cite Krueger2015 and @cite Kremer2016, both (heavily) inspired by @cite Fuhs2007.
This approach heavily benefits from knowing bounds on individual variables, both in terms of its ability to find infeasibility and its performance in general.

In this module, we use smtrat::ICPModule to infer new bounds and call the backend incrementally with growing bounds until the computed upper bounds are met.