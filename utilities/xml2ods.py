#!/usr/bin/env python3

import argparse
from odf import math, table
from odf.opendocument import load, OpenDocumentSpreadsheet
from odf.text import P
import sys
import xml.etree.ElementTree as ET

def load_xml(filename):
	tree = ET.parse(filename)
	root = tree.getroot()
	solvers = []
	for solver in root.findall('./solvers/solver'):
		solvers.append(solver.attrib["solver_id"])
	return solvers,root

def create_cell(text, *args, **kwargs):
	tc = table.TableCell(*args, **kwargs)
	tc.addElement(P(text = text))
	return tc

def create_cell_number(n):
	return create_cell(n, valuetype = 'float', value = n)
def create_cell_string(s = ""):
	return create_cell(s, valuetype = 'string', value = s)
def create_cell_formula(f):
	return create_cell("", valuetype = 'float', formula = 'of:' + f)

def create_row(cells):
	tr = table.TableRow()
	for c in cells:
		tr.addElement(c)
	return tr

def create_row_head(data):
	return create_row([create_cell_string()] + [
		x for d in data for x in [
			create_cell_string(d),
			create_cell_string()
		]
	])

def create_row_data(data):
	return create_row([create_cell_string(data[0])] + [
		x for d in data[1:] for x in [
			create_cell_number(d['runtime']),
			create_cell_string(d['answer'])
		]
	])

def create_stats(solvers, s, min = 2, max = 2):
	if s == 'count':
		runtimes = ''
		counts = '=COUNT(INDIRECT(ADDRESS({0}; CELL("COL")-1) & ":" & ADDRESS({1}; CELL("COL")-1)))'
	else:
		runtimes = '=SUMIF(INDIRECT(ADDRESS({0}; CELL("COL")+1) & ":" & ADDRESS({1}; CELL("COL")+1)); "{2}"; INDIRECT(ADDRESS({0}; CELL("COL")) & ":" & ADDRESS({1}; CELL("COL"))))'
		counts = '=COUNTIF(INDIRECT(ADDRESS({0}; CELL("COL")) & ":" & ADDRESS({1}; CELL("COL"))); "{2}")'

	tr = table.TableRow()
	tr.addElement(create_cell_string(s))
	for _ in solvers:
		if runtimes == '':
			tr.addElement(create_cell_string())
		else:
			tr.addElement(create_cell_formula(runtimes.format(min, max, s)))
		tr.addElement(create_cell_formula(counts.format(min, max, s)))
	return tr

parser = argparse.ArgumentParser(description = "Convert benchmax results to ods.")
parser.add_argument('input', help = 'input file')
args = parser.parse_args()
args.output = args.input.rsplit('.', 1)[0] + '.ods'

solvers,root = load_xml(args.input)

results = []
for file in root.findall('./benchmarks/file'):
	filename = file.attrib["name"]
	res = {}
	for run in file.findall('./run'):
		solver = run.attrib['solver_id']
		res[solver] = {
			'runtime': int(run.find('./results/result[@name="runtime"]').text),
			'answer': run.find('./results/result[@name="answer"]').text,
		}
	results.append([filename] + list(map(lambda x: res[x], solvers)))

doc = OpenDocumentSpreadsheet()
tbl = table.Table(name = "all")
tbl.addElement(create_row_head(solvers))

for r in results:
	tbl.addElement(create_row_data(r))

for s in ['count', 'sat', 'unsat', 'unknown', 'wrong', 'error', 'timeout', 'memout', 'segfault', 'abort']:
	tbl.addElement(create_stats(solvers, s, max = len(results) + 1))

doc.spreadsheet.addElement(tbl)
doc.save(args.output)