#!/usr/bin/env python3

import sys

if len(sys.argv) > 1:
	sys.path.insert(0, sys.argv[1])

from travis_helper import *

jobs = [
	job("0-clang", ["dependencies", "linux", "clang-5.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-5.0", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-6.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-6.0", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-7.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-7.0", "build.sh"]),
	job("1-gcc", ["dependencies", "linux", "g++-7", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["build", "linux", "g++-7", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["dependencies", "linux", "g++-8", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["build", "linux", "g++-8", "j1", "build.sh", "mayfail"]),
	job("2-macos", ["dependencies", "xcode9.3", "build.sh"]),
	job("2-macos", ["build", "xcode9.3", "build.sh", "mayfail"]),
	job("2-macos", ["dependencies", "xcode9.4", "build.sh"]),
	job("2-macos", ["build", "xcode9.4", "build.sh", "mayfail"]),
	job("2-macos", ["dependencies", "xcode10", "build.sh"]),
	job("2-macos", ["build", "xcode10", "build.sh", "mayfail"]),
	job("2-macos", ["dependencies", "xcode10.1", "build.sh"]),
	job("2-macos", ["build", "xcode10.1", "build.sh", "mayfail"]),
	job("3-docs", ["build", "linux", "g++-7", "task.doxygen", "j1", "build.sh"]),
	job("4-tidy", ["build", "linux", "clang-7.0", "task.tidy", "build.sh", "mayfail"]),
]


cached = [
	"$HOME/usr/",
	"$HOME/carl/",
	"build/resources",
]

render_template(jobs, cached)
