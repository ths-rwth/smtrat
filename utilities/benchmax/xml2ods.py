#!/usr/bin/env python3

import argparse
import logging
from odf import config, math, style, table
from odf.opendocument import load, OpenDocumentSpreadsheet
from odf.text import P
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

def create_cell_styles(doc):
	warning = style.Style(family = "table-cell", name = "warning", parentstylename = "Default")
	warning.addElement(
		style.TableCellProperties(backgroundcolor = "#d85c41")
	)
	doc.styles.addElement(warning)

def add_node(parent, node):
	parent.addElement(node)
	return parent.childNodes[-1]
def add_config_item(parent, text, **kwargs):
	return add_node(parent, config.ConfigItem(**kwargs)).addText(text, check_grammar = False)

def freeze_cells(doc, cols = None, rows = None):
	if cols or rows:
		cur = doc.settings
		cur = add_node(cur, config.ConfigItemSet(name = 'ooo:view-settings'))
		cur = add_node(cur, config.ConfigItemMapIndexed(name = 'Views'))
		cur = add_node(cur, config.ConfigItemMapEntry())
		add_config_item(cur, 'view1', name = 'ViewId', type = 'string')
		cur = add_node(cur, config.ConfigItemMapNamed(name = 'Tables'))
		cur = add_node(cur, config.ConfigItemMapEntry(name = 'all'))
		if cols:
			add_config_item(cur, '2', name = 'HorizontalSplitMode', type = 'short')
			add_config_item(cur, str(cols), name = 'HorizontalSplitPosition', type = 'int')
			add_config_item(cur, '1', name = 'PositionRight', type = 'int')
		if rows:
			add_config_item(cur, '2', name = 'VerticalSplitMode', type = 'short')
			add_config_item(cur, str(rows), name = 'VerticalSplitPosition', type = 'int')
			add_config_item(cur, '1', name = 'PositionBottom', type = 'int')

			

def create_cell(text, *args, **kwargs):
	tc = table.TableCell(*args, **kwargs)
	tc.addElement(P(text = text))
	return tc

def create_cell_covered(**kwargs):
	return table.CoveredTableCell(**kwargs)
def create_cell_number(n, **kwargs):
	return create_cell(n, valuetype = 'float', value = n, **kwargs)
def create_cell_string(s = "", check_for_errors = False, **kwargs):
	if check_for_errors and s in ['wrong', 'segfault']:
		kwargs['stylename'] = 'warning'
	return create_cell(s, valuetype = 'string', value = s, **kwargs)
def create_cell_formula(f, **kwargs):
	return create_cell("", valuetype = 'float', formula = 'of:' + f, **kwargs)

def create_row(cells):
	tr = table.TableRow()
	for c in cells:
		tr.addElement(c)
	return tr

def create_row_head(data):
	return create_row([create_cell_string()] + [
		x for d in data for x in [
			create_cell_string(d, numbercolumnsspanned = 2),
			create_cell_covered()
		]
	])

def create_row_data(data):
	return create_row([create_cell_string(data[0])] + [
		x for d in data[1:] for x in [
			create_cell_number(d['runtime']),
			create_cell_string(d['answer'], True)
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
parser.add_argument('--dump', action = 'store_true', help = 'dump xml of input file')
parser.add_argument('input', help = 'input file')
args = parser.parse_args()
args.output = args.input.rsplit('.', 1)[0] + '.ods'

if args.dump:
	doc = load(args.input)
	dom = xml.dom.minidom.parseString(doc.contentxml())
	print(dom.toprettyxml())
	sys.exit(0)

solvers,root = load_xml(args.input)

results = []
for file in root.findall('./benchmarks/file'):
	filename = file.attrib["name"]
	if not filename.endswith('.smt2'):
		continue
	res = {}
	for run in file.findall('./run'):
		solver = run.attrib['solver_id']
		res[solver] = {
			'runtime': int(run.find('./results/result[@name="runtime"]').text),
			'answer': run.find('./results/result[@name="answer"]').text,
		}
	results.append([filename] + list(map(lambda x: res[x], solvers)))

logging.info("Collected results for {} files".format(len(results)))

doc = OpenDocumentSpreadsheet()
create_cell_styles(doc)
freeze_cells(doc, cols = 1, rows = 1)
tbl = table.Table(name = "all")
tbl.addElement(create_row_head(solvers))

for r in results:
	tbl.addElement(create_row_data(r))

for s in ['count', 'sat', 'unsat', 'unknown', 'wrong', 'error', 'timeout', 'memout', 'segfault', 'abort']:
	tbl.addElement(create_stats(solvers, s, max = len(results) + 1))

logging.info("Saving spreadsheet to {}".format(args.output))

doc.spreadsheet.addElement(tbl)
doc.save(args.output)