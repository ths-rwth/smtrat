#!/usr/bin/python

import base64
import hashlib
import json
import os
import os.path
import shutil
import subprocess
import sys
import time
import timeit

start = time.time()

def parseArgs():
	inputfile = sys.argv[1]
	resargs = {}
	args = sys.argv[6:]
	while args != []:
		resargs[args[0][1:]] = args[1]
		args = args[2:]
	return inputfile,resargs

def runCommand(args, cwd, timed = False):
	def f():
		p = subprocess.Popen(args, cwd = cwd, stdout = subprocess.PIPE, stderr = subprocess.PIPE)
		p.wait()
	if timed:
		return timeit.timeit(f, number = 1)
	else:
		f()

class Compiler:
	stdargs = {
		"CMAKE_BUILD_TYPE": "RELEASE",
		"DEVELOPER": "OFF",
		"LOGGING": "OFF",
		"STATICLIB_SWITCH": "OFF",
		"SMTRAT_Strategy": "NewCADAuto"
	}
	builddir = "../../build/"
	cachedir = "cache/"
	
	def getTarget(self, args):
		b = json.dumps(args, sort_keys = True).encode("utf8")
		#encoded = base64.b64encode(b).decode("utf8")
		encoded = hashlib.sha1(b).hexdigest()
		return self.cachedir + "smtrat_" + encoded
	
	def build(self, args):
		args.update(self.stdargs)
		target = self.getTarget(args)
		if not os.path.exists(target):
			#sys.stderr.write("\n+++++ Compiling smtrat for %s\n" % args)
			cmdargs = ["cmake"]
			for k in args: cmdargs = cmdargs + ["-D", "%s=%s" % (k,args[k])]
			cmdargs = cmdargs + ["../"]
			runCommand(cmdargs, self.builddir)
			runCommand(["make", "-j8", "smtrat"], self.builddir)
			shutil.copy(self.builddir + "smtrat", target)
		return target
		

def execute(binary, input):
	return runCommand(["./%s" % binary, input], ".", timed = True)

input,args = parseArgs()

c = Compiler()
binary = c.build(args)

sys.stderr.write("%s %s\n" % (binary,input))
runtime = execute(binary, input)

end = time.time()

print("Result of this algorithm run: SUCCESS,%f,1,%f,0,0" % (end-start,runtime))
