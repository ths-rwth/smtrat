#!/usr/bin/env python3

import glob
import subprocess
import pathlib
from concurrent.futures import ThreadPoolExecutor
import os

benchmark_directory = 'path/to/QF_NRA/'
out_directory = 'out/'
solver = 'path/to/solver/binary'
threads = 8

def relevant(z):
    if re.match(r'\(echo "smtrat.subtropical  [a-zA-Z0-9:/\-.]+ #[0-9]+ \(transformation\)"\)', z):
        return False
    if re.match(r'; smtrat.subtropical  [a-zA-Z0-9:/\-.]+ #[0-9]+ \(transformation\)', z):
        return False
    if z.__contains__('(get-assertions)'):
        return False
    if z.__contains__('(reset)'):
        return False
    if len(z) == 0:
        return False
    if z.__contains__('(set-info :status sat)'):
        return False
    if z.__contains__('(set-info :status unsat)'):
        return False
    return True

def trans(z):
    if z.__contains__('(set-logic undefined)'):
        return '(set-logic QF_LRA)\n'
    else:
        return z


def process(in_filename):
    out_filename = out_directory + in_filename.replace(benchmark_directory, '')
    if os.path.exists(out_filename):
        return True
    pathlib.Path(out_filename).parents[0].mkdir(parents=True, exist_ok=True)

    params = [solver, in_filename, "--validation.channel", "smtrat.subtropical", "--validation.export-smtlib", "--validation.smtlib-filename", out_filename]
    try:
        res = subprocess.run(params, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60*15)
    except subprocess.TimeoutExpired:
        print("Timeout!")
        print("    in " + in_filename)
        return False

    if res.returncode not in [2,3,4]:
        print(res)
        print("    in " + in_filename)
        return False
    else:  
        with open(out_filename, 'r+') as f:
            l=f.readlines()
            l=[trans(z) for z in l if relevant(z)]
        with open(out_filename, 'w') as f:
            f.writelines(l)
        return True

files = glob.glob(benchmark_directory+'**/*.smt2', recursive=True)

with ThreadPoolExecutor(max_workers = threads) as executor:
    res = executor.map(process, files)

    if False in res:
        print("FAIL")
    else:
        print("OK")
