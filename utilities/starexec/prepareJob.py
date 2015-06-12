#!/usr/bin/python

import csv
import sys

if len(sys.argv) < 2:
	print("Usage: " + sys.argv[0] + " JobXXX.csv")
	sys.exit(0)

filename = sys.argv[1]

reader = csv.reader(open(filename, "r"))
writer = csv.writer(open(filename + ".out.csv", "w"))

header = next(reader)
header += ["isok", "same", "solved-unknown", "resout", "incomplete"]
writer.writerow(header)

line = 1
for row in reader:
	line += 1
	additional = [
		'=OR(O{0}, P{0}, Q{0}, R{0})',
		'=L{0}=M{0}',
		'=AND(OR(M{0}="starexec-unknown",M{0}="unknown"),OR(L{0}="sat",L{0}="unsat",L{0}="starexec-unknown",L{0}="unknown"))',
		'=OR(H{0}="timeout (cpu)",H{0}="memout")',
		'=AND(OR(L{0}="starexec-unknown",L{0}="unknown"),ISNUMBER(FIND("QF_BV", B{0})))'
	]
	additional = list(map(lambda s: s.format(str(line)), additional))
	writer.writerow(row + additional)

