#! /usr/bin/python3

import sys
import os
from qepcad_from_smtlib import to_qepcad
from stats import Statistics
from subprocess import Popen, PIPE

qepcad_bin = "/home/jnalbach/code-other/qepcad-B.1.69/qesource/bin/qepcad"
wd = "/home/jnalbach/code-other/qepcad-B.1.69/qesource/bin"
saclib_path = "/home/jnalbach/code-other/saclib2.2.6"
qepcad_path = "/home/jnalbach/code-other/qepcad-B.1.69/qesource"

def run(input) -> str:
    my_env = os.environ.copy()
    my_env['saclib'] = saclib_path
    my_env['qe'] = qepcad_path
    process = Popen(qepcad_bin, stdout=PIPE, stdin=PIPE, universal_newlines=True, cwd = wd, env = my_env)
    try:
        stdout, stderr = process.communicate(input)
    except:
        process.kill()
        return None

    if stderr is not None:
        print("Error: ", stderr)
        print("Error out: ", stdout)
        return None

    try:
        answer = stdout.split("An equivalent quantifier-free formula:")[1].split("\n")[2]
        return answer
    except:
        print("Error: ", stderr)
        print("Error out: ", stdout)
        return None

def get_stats(answer):
    stats = Statistics()
    stats.output_amount_or = answer.count("\\/")
    stats.output_amount_and = answer.count("/\\")
    stats.output_amount_atoms = answer.count("<") + answer.count(">") + answer.count("=") - answer.count("<=") - answer.count(">=") - answer.count("<>")
    return stats

file = sys.argv[1]
if sys.argv[1] == '--stats.print':
    file = sys.argv[2]
with open(file) as f:
    data = f.read()

output = run(to_qepcad(data))
if output:
    #print(output)
    print(get_stats(output))
    exit(2)
else:
    print("(error)")
    exit(10)
