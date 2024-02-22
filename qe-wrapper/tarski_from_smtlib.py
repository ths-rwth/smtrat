from pysmt.walkers import DagWalker, handles
import pysmt.operators as op
from pysmt.typing import BOOL
from from_smtlib_common import *

class TarskiConvert(DagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self, env=env, invalidate_memoization=invalidate_memoization)

    def transform(self, formula):
        return self.walk(formula)

    @handles(op.AND)
    def walk_and(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        return '[' + r' /\ '.join(args) + ']'

    @handles(op.OR)
    def walk_or(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        return '[' + r' \/ '.join(args) + ']'

    @handles(op.NOT)
    def walk_not(self, formula, args, **kwargs):
        assert (len(args) == 1)
        return '[~' + args[0] + ']'

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        assert (formula.is_quantifier())
        ret = ""
        quantifier_type = "all" if formula.is_forall() else "ex"
        ret += quantifier_type + " " + ",".join([escape_var_name(var) for var in formula.quantifier_vars()])  + "[" + args[0] + "]"
        return ret

    @handles(op.SYMBOL)
    def walk_symbol(self, formula, **kwargs):
        assert (formula.is_symbol())
        if (formula.is_symbol(BOOL)):
            raise Exception("booleans not supported")
        return escape_var_name(formula)
    
        # if (formula.is_symbol(BOOL)):
        #     return "[" + escape_var_name(formula) + " < 0]" 
        # else:
        #     return escape_var_name(formula)

    @handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        val = formula.constant_value()  # Just assume that the given formula is an integer
        val_str = str(val).split(".")[0]
        if val < 0:
            return "(" + val_str + ")"
        return val_str

    @handles(op.TIMES)
    def walk_times(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        ret = ""
        for arg in args:
            ret += str(arg) + " "
        return "(" + ret[0:len(ret) - 1] + ")"

    @handles(op.PLUS)
    def walk_plus(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        ret = ""
        for arg in args:
            ret += str(arg) + " + "
        return "(" + ret[0:len(ret) - 3] + ")"

    @handles(op.MINUS)
    def walk_minus(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return "((" + str(args[0]) + ") - (" + str(args[1]) + "))"

    @handles(op.EQUALS)
    def walk_equals(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + str(args[0]) + " = " + str(args[1]) + ']'

    @handles(op.LE)
    def walk_le(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + str(args[0]) + " <= " + str(args[1]) + ']'

    @handles(op.LT)
    def walk_lt(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + str(args[0]) + " < " + str(args[1]) + ']'

    @handles(op.DIV)
    def walk_div(self, formula, args, **kwargs):
        raise Exception("division not supported")
        assert (False and "division not supported")

    @handles(op.IMPLIES)
    def walk_implies(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + args[0] + ' ==> ' + args[1] + ']'

    @handles(op.IFF)
    def walk_iff(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + args[0] + ' <==> ' + args[1] + ']'

def to_tarski(smtlib, sat_mode = False):
    formula = read_formula_from_smtlib(smtlib, sat_mode)
    print(formula)

    converter = TarskiConvert()
    result = converter.transform(formula)

    tarski_input = "(def F [" + result + "]) \n"
    if sat_mode:
        tarski_input += "(qepcad-sat F)\n"
    else:
        tarski_input += "(qepcad-qe F)\n"

    return tarski_input