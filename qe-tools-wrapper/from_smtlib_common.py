from pysmt.smtlib.parser import SmtLibParser
from io import StringIO
from pysmt.shortcuts import Exists, And


def escape_var_name(name):
    return "v"+str(name).replace('_', 'underscore').replace(' ', 'whitespace').replace('.', 'dot').replace('!', 'exclmark').replace('~', 'sim').replace('?', 'questmark')

def read_formula_from_smtlib(smtlib, sat_mode):
    smtlib = smtlib.replace('(apply qe)','')
    parser = SmtLibParser()
    script = parser.get_script(StringIO(smtlib))
    formula = And([command.args[0] for command in script if command.name=='assert'])

    # (< a b c) is not supported by pySMT!

    if sat_mode and len(formula.get_free_variables())>0:
        formula = Exists(formula.get_free_variables(), formula)
    
    return formula