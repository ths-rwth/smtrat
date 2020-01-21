# ESModule {#ESModule}

Uses equations (or Boolean assertions) to eliminate variables from the remaining formula. Let the formula have the form \f$ e \land \varphi' \f$, then we use knowledge gained from \f$ e \f$ to simplify \f$ \varphi' \f$. If \f$ e \f$ is an arithmetic equation such that we can rewrite it to the form \f$ x = t \f$ (with \f$ x \f$ a variable) then we substitute \f$ t \f$ for \f$ x \f$ into \f$ \varphi' \f$. Otherwise we simply replace \f$ e \f$ with \f$ true \f$ in \f$ \varphi' \f$.
This is done recursively in the formula.