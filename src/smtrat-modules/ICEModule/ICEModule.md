# ICEModule {#ICEModule}

This module tries to find simple chains of inequalities that can be combined to form a cycle. It converts constraints of the form \f$ x \geq y + z \f$ to a hypergraph (with an edge going from \f$ x \f$ to \f$ y,z \f$) and uses the coefficients as edge weights.
If this hypergraph contains cycles, these can be used to infer additional constraints on the individual variables. In particular, zero cycles induce equality of variables while negative cycles reveal conflicts.
