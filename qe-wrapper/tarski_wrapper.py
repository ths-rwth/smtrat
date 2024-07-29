#! /usr/bin/python3

import sys
import os
from tarski_from_smtlib import to_tarski
from stats import Statistics
from subprocess import Popen, PIPE

tarski_path = "/home/jnalbach/code-other/tarski/"

def run(input, sat_mode) -> str:
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
    
    if stdout.find('Qepcad failure') != -1:
        print("Error out: ", stdout)
        return "unknown"

    try:
        answer = stdout.split("(qepcad-qe F)\n")[1].split(":tar")[0]
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

sat_mode = data.find('(check-sat)') != -1

try:
    input = to_tarski(data, sat_mode)
except Exception as ex:
    print(ex)
    exit(10)

output = run(input, sat_mode)
if output:
    if sat_mode:
        if output == "unknown":
            print("unknown")
            exit(4)
        elif output.find("false") != -1:
            print("unsat")
            exit(3)
        elif output.find("true") != -1:
            print("sat")
            exit(2)
        #else:
        #     print("sat")
        #     exit(2)
        else:
            print(output)
            print("segfault")
            exit(139)
    else:
        #print(output)
        print(get_stats(output))
        if output == "unknown":
            print("unknown")
            exit(4)
        if output.find("false") != -1:
            exit(3)
        else:
            exit(2)
else:
    print("segfault")
    exit(139)
