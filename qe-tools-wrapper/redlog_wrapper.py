#! /usr/bin/python3

import sys
from redlog_from_smtlib import to_redlog
from stats import Statistics
from subprocess import Popen, PIPE

redlog_path = "/usr/bin/redcsl --nogui -w"

def run(input) -> str:
    process = Popen(redlog_path,stdout=PIPE,stdin=PIPE,universal_newlines=True,shell=True)

    try:
        stdout, stderr = process.communicate(input)
    except:
        process.kill()
        return None

    try:
        # get text between "4:" and "5:"
        answer = stdout.split("5: ")[1].split("6:")[0]
        return answer
    except:
        print("Error out: ", stdout)
        return None

def get_stats(answer):
    stats = Statistics()
    stats.output_amount_atoms = answer.count("=") - 1 + answer.count("<") + answer.count(">") - answer.count("<=") - answer.count(">=") - answer.count("<>")
    stats.output_amount_or = answer.count(" or ")
    stats.output_amount_and = answer.count(" and ")
    return stats

file = sys.argv[1]
if sys.argv[1] == '--stats.print':
    file = sys.argv[2]
with open(file) as f:
    data = f.read()

sat_mode = data.find('(check-sat)') != -1

try:
    input = to_redlog(data, sat_mode)
    #print(input)
except Exception as ex:
    print(ex)
    exit(10)

output = run(input)
if output:
    #print(output)

    if not sat_mode:
        print(get_stats(output))
    if output.find("res := false") != -1:
        if sat_mode:
            print("unsat")
        exit(3)
    else:
        if sat_mode:
            assert(output.find("res := true") != -1)
            print("sat")
        exit(2)
else:
    print("segfault")
    exit(139)
