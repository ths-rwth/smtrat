# This does not work due to weird QEPCAD syntax

import pysmt 
import pysmt.shortcuts as sc
import pyparsing as pp

pp.ParserElement.enablePackrat()

def parse_qepcad(input):
    input = input.replace("/\\","&").replace("\\/","|")
    
    variable = pp.Word(pp.alphas)
    operand = pp.pyparsing_common.integer | variable
    poly = pp.infixNotation(
        operand,
        [
            ("^", 2, pp.opAssoc.RIGHT),
            (pp.Literal("-"), 1, pp.opAssoc.RIGHT),
            (pp.Literal("/"), 2, pp.opAssoc.LEFT),
            (pp.Empty().addParseAction(lambda: "*"), 2, pp.opAssoc.LEFT),
            (pp.Literal("+") | pp.Literal("-"), 2, pp.opAssoc.LEFT),
        ], lpar = pp.Suppress('('), rpar = pp.Suppress(')')
    )
    constraint = pp.infixNotation(
        poly,
        [
            (pp.Literal("<=") | pp.Literal(">=") | pp.Literal("<") | pp.Literal(">") | pp.Literal("=") | pp.Literal("/="), 2, pp.opAssoc.LEFT),
        ], lpar = pp.Suppress('['), rpar = pp.Suppress(']')
    )
    formula = pp.infixNotation(
        constraint,
        [
            (pp.Literal("~"), 1, pp.opAssoc.RIGHT),
            (pp.Literal("&") | pp.Literal("|") | pp.Literal("==>") | pp.Literal("<==>"), 2, pp.opAssoc.LEFT),
            # (pp.Literal("/\\") | pp.Literal("\\/") | pp.Literal("==>") | pp.Literal("<==>"), 2, pp.opAssoc.LEFT),
        ], lpar = pp.Suppress('['), rpar = pp.Suppress(']')
    )
    pnf = pp.ZeroOrMore(pp.Group(pp.Suppress("(") + (pp.Literal("E") | pp.Literal("A")) + variable + pp.Suppress(")"))) + formula
    parsed = pnf.parseString(input).asList()

    def fix_assoc(l):
        if not isinstance(l, list):
            return l

        if len(l) <= 3:
            for i in range(len(l)):
                l[i] = fix_assoc(l[i])
            return l
        else:
            l[0:3] = [l[0:3]] 
            fix_assoc(l)
            return l
        
    parsed[-1] = fix_assoc(parsed[-1])
    return parsed 

def write_smtlib(input):
    symbols = {}

    def f(input):
        if isinstance(input, list):
            if (len(input)==2):
                if (input[0] == "~"):
                    return sc.Not(f(input[1]))
                elif (input[0] == "-"):  
                    return sc.Times(sc.Real(-1), f(input[1]))
                else:
                    print(input)
                    assert(False)
            elif len(input)==3:
                if (input[1] == "+"):
                    return sc.Plus(f(input[0]),f(input[2]))
                elif (input[1] == "-"):
                    return sc.Minus(f(input[0]),f(input[2]))
                elif (input[1] == "*"):
                    return sc.Times(f(input[0]),f(input[2]))
                elif (input[1] == "/"):
                    return sc.Div(f(input[0]),f(input[2]))
                elif (input[1] == "^"):
                    assert(isinstance(input[2], int))
                    return sc.Times([f(input[0]) for i in range(input[2])])
                    # return sc.Pow(f(input[0]),f(input[2]))
                elif (input[1] == "<"):
                    return sc.LT(f(input[0]),f(input[2]))
                elif (input[1] == ">"):
                    return sc.GT(f(input[0]),f(input[2]))
                elif (input[1] == "<="):
                    return sc.LE(f(input[0]),f(input[2]))
                elif (input[1] == ">="):
                    return sc.GT(f(input[0]),f(input[2]))
                elif (input[1] == "="):
                    return sc.Equals(f(input[0]),f(input[2]))
                elif (input[1] == "/="):
                    return sc.Not(sc.Equals(f(input[0]),f(input[2])))
                #elif (input[1] == "/\\"):
                elif (input[1] == "&"):
                    return sc.And(f(input[0]),f(input[2]))
                #elif (input[1] == "\\/"):
                elif (input[1] == "|"):
                    return sc.Or(f(input[0]),f(input[2]))
                elif (input[1] == "==>"):
                    return sc.Implies(f(input[0]),f(input[2]))
                elif (input[1] == "<==>"):
                    return sc.Iff(f(input[0]),f(input[2]))
                else:
                    print(input)
                    assert(False)
            else:
                print(input)
                assert(False)
        elif isinstance(input, str):
            if not input in symbols:
                symbols[input] = sc.Symbol(input, sc.REAL)
            return symbols[input]
        else:
            return sc.Real(input)
        
    res = f(input[-1])
    for e in reversed(input[0:-1]):
        if (e[0] == "E"):
            res = sc.Exists([symbols[e[1]]], res)
        else:
            assert(e[0] == "A")
            res = sc.ForAll([symbols[e[1]]], res)
    return res


def to_smtlib_file(input, out_file):
    parsed = parse_qepcad(input)
    print(parsed)
    smtlib = write_smtlib(parsed)
    script = pysmt.smtlib.script.smtlibscript_from_formula(smtlib, pysmt.logics.NRA)
    with open(out_file, "w", encoding="utf-8") as f:
        script.serialize(f, daggify = False)