import logging
import xml.etree.ElementTree as ET

from . import database

def remove_prefix(s, prefix):
	if s.startswith(prefix):
		return s[len(prefix):]
	return s

def get_solver(s):
	if s.startswith("src.smtrat_master.build."):
		return s[24:]
	if s.startswith("src.smtrat_master2.build."):
		return s[25:]
	return s

# load xml files
def addResult(run, file, timeout, solver_override):
	solver = get_solver(run.attrib["solver_id"])
	if solver in solver_override:
		solver = solver_override[solver]
	filename = file.attrib["name"]
	filename = remove_prefix(filename, "QF_NRA/")
	answer = None
	runtime = None
	for res in run.find('./results'):
		if res.get('name') == 'answer':
			answer = res.text
		elif res.get('name') == 'runtime':
			runtime = int(res.text) / 1000.0
		if answer != None and runtime != None:
			break

	if answer == "memout":
		runtime = timeout + 5
	if answer == "timeout":
		runtime = timeout + 10
	database.insert(solver, filename, answer, runtime)

def load(filename, solver_override = {}):
	logging.info("Loading %s" % filename)
	tree = ET.parse(filename)
	root = tree.getroot()
	timeout = int(root.find("./information/info[@name='timeout']").get('value'))

	for file in root.findall('./benchmarks/*'):
		for run in file.findall('./*'):
			addResult(run, file, timeout = timeout, solver_override = solver_override)

def add_info_result(run, file, solver_override):
	filename = file.attrib["name"]
	filename = remove_prefix(filename, "QF_NRA/")
	solver = get_solver(run.attrib["solver_id"])
	if solver in solver_override:
		solver = solver_override[solver]
	stats = run.find('./statistics')
	if stats is not None:
		for res in stats:
			database.add_file_property(solver, filename, res.get('name'), res.text)

def load_info(filename, solver_override = {}):
	logging.info("Loading infos from %s" % filename)
	tree = ET.parse(filename)
	root = tree.getroot()

	for file in root.findall('./benchmarks/*'):
		for run in file.findall('./*'):
			add_info_result(run, file, solver_override = solver_override)