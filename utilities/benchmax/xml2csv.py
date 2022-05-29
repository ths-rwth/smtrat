#!/usr/bin/env python3

import argparse
import logging
import csv
import sys
import xml.etree.ElementTree as ET
import xml.dom.minidom

logging.basicConfig(format='[%(levelname)s] %(message)s', level=logging.DEBUG)

def load_xml(filename):
	logging.info("Loading {}".format(filename))
	tree = ET.parse(filename)
	root = tree.getroot()
	solvers = []
	for solver in root.findall('./solvers/solver'):
		solvers.append(solver.attrib["solver_id"])
	logging.info("Loaded solvers: {}".format(solvers))
	return solvers,root

def add_node(parent, node):
	parent.addElement(node)
	return parent.childNodes[-1]

parser = argparse.ArgumentParser(description = "Convert benchmax results to csv.")
parser.add_argument('--dump', action = 'store_true', help = 'dump xml of input file')
parser.add_argument('input', help = 'input file')
args = parser.parse_args()
args.output = args.input.rsplit('.', 1)[0] + '.csv'

out = open(args.output, 'w')
writer = csv.writer(out)

if args.dump:
	doc = open(args.input, 'r')
	dom = xml.dom.minidom.parseString(doc.contentxml())
	print(dom.toprettyxml())
	sys.exit(0)

solvers,root = load_xml(args.input)

results = {}
keys = set()
for file in root.findall('./benchmarks/file'):
	filename = file.attrib["name"]
	if not filename.endswith(".smt2"):
		continue
	logging.info("Checking file {}".format(filename))
	res = {}
	for run in file.findall('./run'):
		for stat in run.findall('./statistics/stat'):
			res[stat.get('name')] = stat.text
		for result in run.findall('./results/result'):
			res[result.get('name')] = result.text
	keys = keys.union(set(list(res.keys())))
	results[filename] = res

logging.info("Collected results for {} files".format(len(results)))

head = sorted(list(keys))
writer.writerow(['file'] + head)

for name,res in results.items():
	row = [name]
	for key in head:
		row = row + [res.get(key)]
	writer.writerow(row)

logging.info("Saving spreadsheet to {}".format(args.output))

