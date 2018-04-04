#!/usr/bin/env python3

import sys

if len(sys.argv) > 1:
	sys.path.insert(0, sys.argv[1])

from travis_helper import *

jobs = [
	job("0-clang", ["build", "linux", "clang-3.8", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-3.9", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-4.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-5.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-6.0", "build.sh"]),
	job("1-gcc", ["dependencies", "linux", "g++-5", "j1", "build.sh"]),
	job("1-gcc", ["build", "linux", "g++-5", "j1", "build.sh"]),
	job("1-gcc", ["dependencies", "linux", "g++-6", "j1", "build.sh"]),
	job("1-gcc", ["build", "linux", "g++-6", "j1", "build.sh"]),
	job("1-gcc", ["dependencies", "linux", "g++-7", "j1", "build.sh"]),
	job("1-gcc", ["build", "linux", "g++-7", "j1", "build.sh"]),
	job("2-macos", ["build", "xcode7.3", "build.sh"]),
	job("2-macos", ["build", "xcode8.2", "build.sh"]),
	job("2-macos", ["build", "xcode8.3", "build.sh"]),
	job("3-docs", ["build", "linux", "g++-6", "task.doxygen", "j1", "build.sh"]),
]

render_template(jobs)
