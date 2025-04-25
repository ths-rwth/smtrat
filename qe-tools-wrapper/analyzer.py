#! /usr/bin/python3

import sys

import pysmt
import pysmt.oracles
import pysmt.shortcuts
import pysmt.rewritings
import pysmt.operators as op
from pysmt.typing import BOOL,REAL,INT
from pysmt.smtlib.parser import SmtLibParser
from io import StringIO
import sympy as sp
import sympy.abc
from pysmt.walkers import DagWalker, handles

import warnings
warnings.filterwarnings("ignore")

class PolyConverter(DagWalker):
    @handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        return sp.Rational(formula.constant_value())

    @handles(op.SYMBOL)
    def walk_symbol(self, formula, **kwargs):
        return sp.symbols(formula.symbol_name())

    @handles(op.TIMES)
    def walk_times(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        res = 1
        for arg in args:
            res *= arg
        return res

    @handles(op.PLUS)
    def walk_plus(self, formula, args, **kwargs):
        assert (len(args) >= 2)
        return sum(args)

    @handles(op.MINUS)
    def walk_minus(self, formula, args, **kwargs):
        if len(args) == 1:
            return -args[0]
        else:
            return args[0]-sum(args[1:])

def pysmt_to_sympy(formula):
    assert(formula.is_theory_relation())
    assert(len(formula.args())==2)
    try:
        converter = PolyConverter()
        result = converter.walk(formula.args()[0]-formula.args()[1])
        return sp.poly_from_expr(result)[0]
    except sympy.polys.polyerrors.PolificationFailed as ex:
        return None

class PolynomialOracle(pysmt.walkers.DagWalker):
    def get_polynomials(self, formula):
        self.set_function(self.walk_helper, *op.ALL_TYPES)
        return self.walk(formula)

    def walk_helper(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if (len(args)==0):
            return frozenset([])
        elif formula.is_theory_relation():
            tmp = pysmt_to_sympy(formula)
            if not tmp is None:
                return frozenset([tmp])
            else:
                return frozenset([])
        else:
            return frozenset([x for s in args for x in s]) 

def num_vars(f):
    vars = pysmt.oracles.FreeVarsOracle().get_free_variables(f)
    return len(vars)

def num_vars_real(f):
    vars = pysmt.oracles.FreeVarsOracle().get_free_variables(f)
    vars = [v for v in vars if v.is_symbol(REAL)]
    return len(vars)

def num_vars_int(f):
    vars = pysmt.oracles.FreeVarsOracle().get_free_variables(f)
    vars = [v for v in vars if v.is_symbol(INT)]
    return len(vars)

def num_vars_arith(f):
    return num_vars_real(f)+num_vars_int(f)

def num_vars_bool(f):
    vars = pysmt.oracles.FreeVarsOracle().get_free_variables(f)
    vars = [v for v in vars if v.is_symbol(BOOL)]
    return len(vars)

def num_atoms(f):
    vars = pysmt.oracles.AtomsOracle().get_atoms(f)
    return len(vars)

def num_atoms_theory(f):
    vars = pysmt.oracles.AtomsOracle().get_atoms(f)
    vars = [v for v in vars if v.is_theory_relation()]
    return len(vars)

def num_atoms_theory_eq(f):
    vars = pysmt.oracles.AtomsOracle().get_atoms(f)
    vars = [v for v in vars if v.is_equals()]
    return len(vars)

def num_atoms_theory_le(f):
    vars = pysmt.oracles.AtomsOracle().get_atoms(f)
    vars = [v for v in vars if v.is_le()]
    return len(vars)

def num_atoms_theory_lt(f):
    vars = pysmt.oracles.AtomsOracle().get_atoms(f)
    vars = [v for v in vars if v.is_lt()]
    return len(vars)

def dag_num_nodes_bool(f):
    return pysmt.oracles.SizeOracle().get_size(f,pysmt.oracles.SizeOracle.MEASURE_BOOL_DAG)

def dag_num_nodes(f):
    return pysmt.oracles.SizeOracle().get_size(f,pysmt.oracles.SizeOracle.MEASURE_DAG_NODES)

def dag_depth(f):
    return pysmt.oracles.SizeOracle().get_size(f,pysmt.oracles.SizeOracle.MEASURE_DEPTH)

def dag_depth_bool(f):
    class Oracle(pysmt.walkers.DagWalker):
        def get_size(self, formula):
            self.set_function(self.walk_helper, *op.ALL_TYPES)
            return self.walk(formula)

        def walk_helper(self, formula, args, **kwargs):
            #pylint: disable=unused-argument
            is_leaf = (len(args) == 0) or formula.is_theory_relation()
            return 1 + (0 if is_leaf else max(args))
    return Oracle().get_size(f)

def cnf_num_clauses(f):
    if pysmt.oracles.QuantifierOracle().is_qf(f):
        return len(pysmt.rewritings.cnf_as_set(f))
    else:
        return 'none'

def pnf_num_quant(f):
    class Oracle(pysmt.walkers.DagWalker):
        def get_size(self, formula):
            self.set_function(self.walk_helper, *op.ALL_TYPES)
            return self.walk(formula)

        def walk_helper(self, formula, args, **kwargs):
            #pylint: disable=unused-argument
            is_quant = formula.is_quantifier()
            return sum(args) + 0 if not is_quant else len(formula.quantifier_vars())
    return Oracle().get_size(pysmt.rewritings.prenex_normal_form(f))

def pnf_num_quant_alt(f):
    return '?' # not implemented yet

def arith_max_total_degree(polys):
    return max([0] + [max([0] + [sum(m) for m in p.monoms()]) for p in polys])

def arith_max_degree(polys):
    return max([0] + [max(p.degree_list()) for p in polys])

def arith_sum_total_degree(polys):
    return sum([max([0] + [sum(m) for m in p.monoms()]) for p in polys])

def arith_sum_total_degree_mon(polys):
    return sum([sum([sum(m) for m in p.monoms()]) for p in polys])

def arith_sum_degree(polys):
    return sum([max(p.degree_list()) for p in polys])

def arith_num_monoms(polys):
    return sum([len(p.monoms()) for p in polys])

if len(sys.argv) < 2:
    print("Usage: python analyzer.py <smtlib_file>")
    sys.exit(1)

def read_smtlib(smtlib):
    smtlib = smtlib.replace('(apply qe)','')
    parser = SmtLibParser()
    script = parser.get_script(StringIO(smtlib))
    formula = pysmt.shortcuts.And([command.args[0] for command in script if command.name=='assert'])
    info = [command.args[1] for command in script if command.name=='set-info' and command.args[0] == ':status']
    status = info[0] if len(info)==1 else 'unknown'
    return formula,status
 

file_path = sys.argv[1]
with open(file_path, 'r') as f:
    formula,answer = read_smtlib(f.read())
    polys = PolynomialOracle().get_polynomials(formula)

try:
    print(
    '''(:formula (
        :answer                      ''' + str(answer)  + '''
        :num_vars                    ''' + str(num_vars(formula))  + '''
        :num_vars_real               ''' + str(num_vars_real(formula))  + '''
        :num_vars_int                ''' + str(num_vars_int(formula))  + '''
        :num_vars_arith              ''' + str(num_vars_arith(formula))  + '''
        :num_vars_bool               ''' + str(num_vars_bool(formula))  + '''
        :num_atoms                   ''' + str(num_atoms(formula))  + '''
        :num_atoms_theory            ''' + str(num_atoms_theory(formula))  + '''
        :num_atoms_theory_eq         ''' + str(num_atoms_theory_eq(formula))  + '''
        :num_atoms_theory_le         ''' + str(num_atoms_theory_le(formula))  + '''
        :num_atoms_theory_lt         ''' + str(num_atoms_theory_lt(formula))  + '''
        :dag_num_nodes               ''' + str(dag_num_nodes(formula))  + '''
        :dag_depth                   ''' + str(dag_depth(formula))  + '''
        :dag_num_nodes_bool          ''' + str(dag_num_nodes_bool(formula))  + '''
        :dag_depth_bool              ''' + str(dag_depth_bool(formula))  + '''
        :pnf_num_quant               ''' + str(pnf_num_quant(formula))  + '''
        :pnf_num_quant_alt           ''' + str(pnf_num_quant_alt(formula))  + '''
        :arith_max_total_degree      ''' + str(arith_max_total_degree(polys))  + '''
        :arith_max_degree            ''' + str(arith_max_degree(polys))  + '''
        :arith_sum_total_degree      ''' + str(arith_sum_total_degree(polys))  + '''
        :arith_sum_degree            ''' + str(arith_sum_degree(polys))  + '''
        :arith_sum_total_degree_mon  ''' + str(arith_sum_total_degree_mon(polys))  + '''
        :arith_num_polys             ''' + str(len(polys))  + '''
        :arith_num_monoms            ''' + str(arith_num_monoms(polys))  + '''
    ))'''
    )
    #         :cnf_num_clauses         ''' + str(cnf_num_clauses(formula))  + '''
    exit(4)
except Exception as ex:
    raise ex
    print("segfault")
    exit(139)