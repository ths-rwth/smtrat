from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import DagWalker, handles
import pysmt.operators as op
from io import StringIO

class QepcadConvert(DagWalker):
    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self, env=env, invalidate_memoization=invalidate_memoization)
        self.quantified_vars = []

    def transform(self, formula):
        return self.walk(formula)

    @handles(op.AND)
    def walk_and(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        return '[' + r' /\ '.join(args) + ']'

    @handles(op.OR)
    def walk_or(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + r' \/ '.join(args) + ']'

    @handles(op.NOT)
    def walk_not(self, formula, args, **kwargs):
        assert (len(args) == 1)
        return '[~' + args[0] + ']'

    @handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        assert (formula.is_quantifier())
        ret = ""
        quantifier_type = "A" if formula.is_forall() else "E"
        for var in formula.quantifier_vars():
            ret += "(" + quantifier_type + " " + str(var) + ")"
        if args[0].startswith('(A') or args[0].startswith('(E'):
            ret += args[0]
        else:
            ret += "[" + args[0] + "]"
        self.quantified_vars = list(formula.quantifier_vars()) + self.quantified_vars
        return ret

    @handles(op.SYMBOL)
    def walk_symbol(self, formula, **kwargs):
        assert (formula.is_symbol())
        return str(formula)

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
        return ret[0:len(ret) - 1]

    @handles(op.PLUS)
    def walk_plus(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        ret = ""
        for arg in args:
            ret += str(arg) + " + "
        return ret[0:len(ret) - 3]

    @handles(op.MINUS)
    def walk_minus(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return "(" + str(args[0]) + ") - (" + str(args[1]) + ")"

    @handles(op.EQUALS)
    def walk_equals(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return str(args[0]) + " = " + str(args[1])

    @handles(op.LE)
    def walk_le(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return str(args[0]) + " <= " + str(args[1])

    @handles(op.LT)
    def walk_lt(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return str(args[0]) + " < " + str(args[1])

    @handles(op.DIV)
    def walk_div(self, formula, args, **kwargs):
        assert (False and "Division not supported")

    @handles(op.IMPLIES)
    def walk_implies(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + args[0] + ' ==> ' + args[1] + ']'

    @handles(op.IFF)
    def walk_iff(self, formula, args, **kwargs):
        assert (len(args) == 2)
        return '[' + args[0] + ' <==> ' + args[1] + ']'

def to_qepcad(smtlib):
    smtlib = smtlib.replace('(apply qe)','')
    parser = SmtLibParser()
    script = parser.get_script(StringIO(smtlib))
    formula = [command.args[0] for command in script if command.name=='assert'][0]

    converter = QepcadConvert()
    result = converter.transform(formula)

    qepcad_input = """[QEPCAD Tests] \n"""
    qepcad_input += "(" + ",".join([str(x) for x in (list(formula.get_free_variables()) + converter.quantified_vars)]) + ")" + "\n"
    qepcad_input += str(len(formula.get_free_variables())) + " \n"  # Number of free variables
    qepcad_input += result + ". \n" 
    qepcad_input += "go\n"
    qepcad_input += "go\n"
    qepcad_input += "go\n"
    qepcad_input += "pdq\n"
    qepcad_input += "solution-extension E\n"
    qepcad_input += "finish\n"

    return qepcad_input