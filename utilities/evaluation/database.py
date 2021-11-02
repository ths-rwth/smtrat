import atexit
from functools import lru_cache
import logging
import sqlite3


# SQLite stuff
def init():
	#conn = sqlite3.connect(":memory:")
	conn = sqlite3.connect("db.db")
	conn.row_factory = sqlite3.Row
	return conn
	
def reset():
	conn.execute('''DROP TABLE IF EXISTS files''')
	conn.execute('''CREATE TABLE files (
		id integer primary key autoincrement,
		filename text,
		UNIQUE(filename)
	)''')
	conn.execute('''DROP TABLE IF EXISTS file_properties''')
	conn.execute('''CREATE TABLE file_properties (
		solver string,
		file integer,
		name text,
		value text
	)''')
	conn.execute('''CREATE INDEX fp_solver ON file_properties (solver)''')
	conn.execute('''CREATE INDEX fp_file ON file_properties (file)''')
	conn.execute('''CREATE INDEX fp_name ON file_properties (name)''')

	conn.execute('''DROP TABLE IF EXISTS data''')
	conn.execute('''CREATE TABLE data (solver text, file integer, answer text, runtime real)''')
	conn.execute('''CREATE INDEX data_file ON data (file)''')
	conn.execute('''CREATE INDEX data_solver ON data (solver)''')

conn = init()
#reset()

def commit():
	conn.commit()

def execute(query, *args):
	return conn.execute(query, *args)

def insert(solver, filename, answer, runtime):
	conn.execute('INSERT INTO data (solver, file, answer, runtime) VALUES (?,?,?,?)', (solver, file_id(filename), answer, runtime))

def get_incorrect_from(solver):
	cur = conn.execute('''
	SELECT
		f.filename,
		d.answer AS solver,
		fp.value AS correct
	FROM data AS d
	INNER JOIN file_properties AS fp
		ON (d.file = fp.file AND fp.name = 'formula_answer')
	INNER JOIN files AS f
		ON (d.file = f.id)
	WHERE 
		d.answer IN ('sat', 'unsat') AND 
		fp.value IN ('sat', 'unsat') AND 
		d.answer != fp.value
	''')
	return cur.fetchall()

def update_reference_from(solver):
	cur = conn.execute('''
	UPDATE file_properties AS fp
	SET value = (
		SELECT answer
		FROM data AS d
		WHERE 
			d.file = fp.file AND d.solver = ? AND
			d.answer IN ('sat', 'unsat')
	)
	WHERE EXISTS (
		SELECT answer
		FROM data
		WHERE 
			data.file = fp.file AND data.solver = ? AND
			data.answer IN ('sat', 'unsat')
	) AND name = 'formula_answer' AND value = 'unknown'
	''', (solver, solver))
	logging.info('Used %s as new reference solver, marking another %s as solved.' % (solver, cur.rowcount))

def use_solver_as_reference(solver):
	for v in get_incorrect_from(solver):
		logging.error('ERROR: Solver %s has incorrect result on %s: %s but should be %s' % (solver, v['filename'], v['solver'], v['correct']))
	update_reference_from(solver)

def solved_within_time(solver, timeout):
	cur = conn.execute('''
		SELECT COUNT(file) AS cnt FROM data
		WHERE solver = ? AND runtime < ? AND answer IN ('sat', 'unsat')
	''', (solver, timeout))
	return cur.fetchone()["cnt"]

@lru_cache()
def file_id(filename):
	conn.execute('INSERT OR IGNORE INTO files (filename) VALUES(?)', (filename,))
	cur = conn.execute('SELECT id FROM files WHERE filename = ?', (filename,))
	return cur.fetchone()[0]

def add_file_property(solver, filename, name, value):
	conn.execute('INSERT INTO file_properties (solver, file, name, value) VALUES (?,?,?,?)', (solver, file_id(filename), name, value))

def getSolvers():
	cur = conn.execute('SELECT solver FROM data GROUP BY solver')
	return list(map(lambda s: s["solver"], cur.fetchall()))

def get_solvers():
	return getSolvers()

def getPossibleAnswers():
	cur = conn.execute('SELECT answer FROM data GROUP BY answer')
	return list(map(lambda s: s["answer"], cur.fetchall()))

@lru_cache(maxsize=1)
def numberOfFiles():
	cur = conn.execute('SELECT COUNT(DISTINCT file) AS cnt FROM data')
	return cur.fetchone()["cnt"]

def cleanupMemouts():
	conn.execute('''
		UPDATE data
		SET answer = 'memout'
		WHERE answer = 'segfault'
		''')

def dumpData():
	for row in conn.execute('''SELECT * FROM data LIMIT 1000'''):
		print(row)

def getCummulativeData(solver):
	cur = conn.execute('''
		SELECT runtime, COUNT(runtime) AS cnt
		FROM data
		WHERE solver = ? AND answer in ('sat', 'unsat')
		GROUP BY runtime
		ORDER BY runtime ASC
		''', (solver,))
	return cur.fetchall()

@lru_cache(maxsize=1)
def getStats():
	cur = conn.execute('''
	SELECT solver,
		COUNT(CASE WHEN answer='sat' THEN 1 END) AS sat,
		COUNT(CASE WHEN answer='unsat' THEN 1 END) AS unsat,
		COUNT(CASE WHEN answer IN ('sat','unsat') THEN 1 END) AS solved,
		COUNT(CASE WHEN answer='timeout' THEN 1 END) AS timeout,
		COUNT(CASE WHEN answer IN ('memout','segfault') THEN 1 END) AS memout,
		AVG(CASE WHEN answer='sat' THEN runtime END) AS avgsattime,
		AVG(CASE WHEN answer='unsat' THEN runtime END) AS avgunsattime,
		AVG(CASE WHEN answer IN ('sat','unsat') THEN runtime END) AS avgtime
	FROM data
	GROUP BY solver
	''')
	return cur.fetchall()

def getAllStats(solver):
	cur = conn.execute('''
	SELECT answer,
		COUNT(answer) AS cnt,
		SUM(runtime) AS time
	FROM data
	WHERE solver = ?
	GROUP BY answer
	''', (solver,))
	return { r["answer"]: (r["cnt"], r["time"]) for r in cur.fetchall() }

def solvedByXnotY(x, y):
	cur = conn.execute('''
	SELECT COUNT(file) AS cnt
	FROM data
	WHERE solver = ? AND answer IN ('sat','unsat') AND file IN (
		SELECT file FROM data WHERE solver = ? AND answer NOT IN ('sat','unsat')
	)
	''', (x,y))
	return cur.fetchone()["cnt"]

def solvedNotByX(x):
	return conn.execute('''
	SELECT file
	FROM data
	WHERE solver = ? AND answer NOT IN ('sat','unsat') LIMIT 10
	''', (x,)).fetchall()

def scatterData(s1, s2, where = None):
	if where == None:
		where = '1==1'
	cur = conn.execute('''
	SELECT 
		d1.answer AS answer1,
		d1.runtime AS runtime1,
		d2.answer AS answer2,
		d2.runtime AS runtime2
	FROM data AS d1
	INNER JOIN data AS d2
		ON (d1.file = d2.file AND d1.solver = ? AND d2.solver = ?)
	WHERE %s
	''' % where, (s1, s2))
	return cur.fetchall()

def file_statistics():
	cur = conn.execute('''
	SELECT 
		name,
		MIN(CAST(value as REAL)),
		AVG(CAST(value as REAL)),
		MAX(CAST(value as REAL))
	FROM file_properties
	GROUP BY solver, name
	''')
	return cur.fetchall()

def file_info_data(property):
	cur = conn.execute('''
	SELECT
		CAST(value as REAL) AS value,
		COUNT(value) AS count
	FROM file_properties
	WHERE name = ?
	GROUP BY value
	ORDER BY value ASC
	''', (property,))
	return cur.fetchall()

def file_info_data_str(property):
	cur = conn.execute('''
	SELECT
		value,
		COUNT(value) AS count
	FROM file_properties
	WHERE name = ?
	GROUP BY value
	ORDER BY value ASC
	''', (property,))
	return cur.fetchall()

def file_with_info_count(properties):
	where = []
	for p in properties:
		upper = lower = ''
		if p[1] is not None:
			lower = 'AND CAST(fp.value AS REAL) >= %s' % p[1]
		if p[2] is not None:
			upper = 'AND CAST(fp.value AS REAL) <= %s' % p[2]
		q = '(fp.name = \'%s\' %s %s)' % (p[0], lower, upper)
		where.append(q)
	where = " OR ".join(where)
	cur = conn.execute('''
	SELECT
		COUNT(f.id)
	FROM files AS f
	INNER JOIN file_properties AS fp
		ON (f.id = fp.file)
	WHERE
		(%s)
	GROUP BY f.id
	''' % where)
	return len(cur.fetchall())
