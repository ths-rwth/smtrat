#!/usr/bin/env python3

import subprocess
import sys
import pathlib

def run(command):
	res = subprocess.run(command)#, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	return res

filename = sys.argv[3]
out = sys.argv[2]
solver = sys.argv[1]

out_filename = out + filename.replace("../", "")

pathlib.Path(out_filename).parents[0].mkdir(parents=True, exist_ok=True)
params = [solver, filename, "--validation.channel", "smtrat.subtropical", "--validation.export-smtlib", "--validation.smtlib-filename", out_filename]
res = run(params)
#print(' '.join(params))
#print(res)

with open(out_filename, 'r+') as f:
    l=f.readlines()
    l=[z.replace('(set-info :status sat)','').replace('(set-info :status unsat)','') for z in l]
with open(out_filename, 'w') as f:
    f.writelines(l)

exit(res.returncode)