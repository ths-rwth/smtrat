# LVEModule {#LVEModule}

This module aims to eliminate lone variables that only occur once.
We call a variable a lone variable if it only occurs in a single constraint.
Furthermore we only try to eliminate the variable if this constraint is a top-level constraint.
