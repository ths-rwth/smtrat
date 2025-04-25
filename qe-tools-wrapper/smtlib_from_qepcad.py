import sys
import os
from tarski_from_smtlib import to_tarski
from stats import Statistics
from subprocess import Popen, PIPE

tarski_path = "/home/jnalbach/code-other/tarski1.28/"

def run(input) -> str:
    my_env = os.environ.copy()
    my_env['saclib'] = tarski_path + 'saclib2.2.7'
    my_env['qe'] = tarski_path + 'qesource'
    my_env['PATH'] = my_env['PATH'] + ':' + tarski_path + 'qesource/bin'
    process = Popen(tarski_path + 'bin/tarski', stdout=PIPE, stdin=PIPE, universal_newlines=True, cwd = tarski_path + 'bin/', env = my_env)
    try:
        stdout, stderr = process.communicate(input)
    except:
        process.kill()
        return None
    if stderr is not None:
        print("Error: ", stderr)
        print("Error out: ", stdout)
        return None
    return stdout
    

def to_smtlib(input):
    formula = input[input.find('['):]
    quantifiers = []
    if input.find('[') > 0:
        quantifiers = input[1:input.find('[')-1].split(')(')

    res = run("""(def F [""" + formula + """])
(smtlib-store F \"""" + os.getcwd() + """/tmp.smt2\")""")
    assert(res)
    
    with open("tmp.smt2", 'r') as f:
        output = f.readlines()
    assert(output)

    assert(output[-1].startswith('(check-sat)'))
    output[-1] = "(apply qe)\n"

    assert(output[0].startswith('(set-logic'))
    output[0] = "(set-logic NRA)\n"

    assert(output[-2].startswith('(assert '))
    formula = output[-2][8:-2]
    qvars = []
    for q in reversed(quantifiers):
        quantifier_type = "forall" if q.split(' ')[0] == 'A' else "exists"
        formula = "(" + quantifier_type + " ((" + q.split(' ')[1] + " Real)) " + formula + ")"
        qvars.append(q.split(' ')[1])
    output[-2] = "(assert " + formula + ")\n"

    for i in range(len(output)):
        for v in qvars:
            if output[i].startswith('(declare-fun ' + v + ' () Real)'):
                output[i] = ''
        if output[i].startswith('(set-info'):
            output[i] = ''

    return ''.join(output)

