#! /usr/bin/python3

import sys
import subprocess
import os
import time

def write_formula(input_file, qe_result_formula, out_file):
    with open(input_file) as f:
        original_data = f.read()
    decls = []
    variables = []
    asserts = []
    for line in original_data.splitlines():
        if line.startswith('(declare-'):
            variables.append(line.split(' ')[1])
        if line.startswith('(assert '):
            asserts.append(line.strip()[len('(assert '):-1])
    if len(asserts) > 0:
        original_formula = asserts[0] if len(asserts) == 1 else '(and ' + ' '.join(asserts) + ')'
    else:
        original_formula = 'true'
    if len(variables) > 0:
        formula = '(assert (forall (' + ' '.join(['(' + v + ' Real)' for v in variables]) + ') (= ' + original_formula + ' ' + qe_result_formula + ')))'
    else:
        formula = '(assert (= ' + original_formula + ' ' + qe_result_formula + '))'
    script = '(set-logic NRA)\n' + '\n'.join(decls) + '\n' + formula + '\n' + '(check-sat)'
    with open(out_file, 'w') as f:
        f.write(script)

def run_smtlib_qe_tool(binary, input_file):
    try: 
        #res = subprocess.run([binary, input_file], capture_output=True, timeout=60)
        res = subprocess.run(binary + " " + input_file, capture_output=True, timeout=60, shell=True)
    except subprocess.TimeoutExpired:
        return None
        
    if res.stderr.decode('utf-8') != '' or res.stdout.decode('utf-8') == 'unknown':
        return None
    else:
        return res.stdout.decode('utf-8').rstrip('\n')
    
def run_smtlib_checker(binary, input_file):
    try: 
        res = subprocess.run([binary, input_file], capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        return None

    #print(res.stdout)

    if res.stderr.decode('utf-8').strip() != '':
        return None
    elif res.stdout.decode('utf-8').strip() == "sat":
        return True
    elif res.stdout.decode('utf-8').strip() == "unsat": 
        return False
    elif res.stdout.decode('utf-8').strip() == "unknown":
        return None

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


def verify_result(tool_binary, verifier_binary, input_file):
    print("Verifying", input_file)

    start = time.time()
    qe_result_data = run_smtlib_qe_tool(tool_binary, input_file)
    end = time.time()

    if qe_result_data is None or qe_result_data == '':
        print(f"\t {bcolors.WARNING}tool failed{bcolors.ENDC}")
        return 5
    else:
        write_formula(input_file, qe_result_data, "tmp_verify.smt2")
        res = run_smtlib_checker(verifier_binary, "tmp_verify.smt2")
        if res is None:
            print(f"\t {bcolors.WARNING}verifier failed{bcolors.ENDC}")
            return 4
        elif res == True:
            print(f"\t {bcolors.OKGREEN}ok{bcolors.ENDC} ({end - start})s")
            return 2
        elif res == False:
            print(f"\t {bcolors.FAIL}wrong{bcolors.ENDC} ({end - start})s")
            return 3


tool_binary = sys.argv[1]
verifier_binary = sys.argv[2]
input_file = sys.argv[3]

if os.path.isfile(input_file):
    returncode = verify_result(tool_binary, verifier_binary, input_file)
    exit(returncode)
else:
    for subdir, dirs, files in os.walk(input_file):
        for file in files:
            filepath = os.path.join(subdir, file)
            verify_result(tool_binary, verifier_binary, filepath)