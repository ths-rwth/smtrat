#!/usr/bin/env python 

import re
import subprocess
import sys

filename = sys.argv[1]
responsere = re.compile(b"((?:un)?sat)\s*$")
solvers = {
	"smtrat": ["./smtrat"],
	"z3": ["z3"],
}

def run(command):
	res = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
	if res.returncode in [2,3]:
		print("Got proper smtrat result")
		return {2: "sat", 3: "unsat"}[res.returncode]
	match = responsere.search(res.stdout)
	if match != None:
		return match.group(1).decode("utf-8")
	return "unknown"

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

d = { k: run(v + [filename]) for (k,v) in solvers.items() }	
sys.exit(compare(d))
