#!/usr/bin/env python 

import re
import subprocess
import sys

def response_smtrat(res):
	if res.returncode in [2,3]:
		print("Got proper smtrat result")
		return {2: "sat", 3: "unsat"}[res.returncode]
	match = re.search(b"((?:un)?sat)\s*$", res.stdout)
	if match != None:
		return match.group(1).decode("utf-8")
	return "unknown"

def response_z3(res):
	if res.returncode == 1:
		return "unknown"
	match = re.search(b"^((?:un)?sat)", res.stdout)
	if match != None:
		return match.group(1).decode("utf-8")
	return "unknown"

filename = sys.argv[1]
solvers = {
	"smtrat": (["./smtrat-shared"], response_smtrat),
	"z3": (["z3"], response_z3),
}

def run(command, response):
	res = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	return response(res)

def compare(runs):
	results = {"sat": 0, "unsat": 0, "unknown": 0}
	for s,r in runs.items():
		results[r] += 1
		print("%s: %s" % (s,r))
	if results["unknown"] > 0:
		print("Had unknowns -> 2")
		return 2
	if results["sat"] > 0 and results["unsat"] > 0:
		print("Solvers disagreed -> 1")
		return 1
	print("Solvers agreed -> 0")
	return 0

d = { k: run(v[0] + [filename], v[1]) for (k,v) in solvers.items() }	
sys.exit(compare(d))
